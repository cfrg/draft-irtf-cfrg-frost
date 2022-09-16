#!/usr/bin/sage
# vim: syntax=python

import os
import sys
import json

from ed25519_rfc8032 import verify_ed25519_rfc8032, point_compress, secret_to_public_raw

try:
    from sagelib.groups import GroupRistretto255, GroupEd25519, GroupEd448, GroupP256, GroupSecp256k1
    from sagelib.hash import HashEd25519, HashEd448, HashRistretto255, HashP256, HashSecp256k1
except ImportError as e:
    sys.exit("Error loading preprocessed sage files. Try running `make setup && make clean pyfiles`. Full error: " + e)

_as_bytes = lambda x: x if isinstance(x, bytes) else bytes(x, "utf-8")

def to_hex(byte_string):
    if isinstance(byte_string, str):
        return "".join("{:02x}".format(ord(c)) for c in byte_string)
    if isinstance(byte_string, bytes):
        return "" + "".join("{:02x}".format(c) for c in byte_string)
    assert isinstance(byte_string, bytearray)
    return ''.join(format(x, '02x') for x in byte_string)


def random_bytes(n):
    return os.urandom(n)

# https://cfrg.github.io/draft-irtf-cfrg-frost/draft-irtf-cfrg-frost.html#name-lagrange-coefficients
def derive_lagrange_coefficient(G, i, L):
    assert(i != 0)
    for j in L:
      assert(j != 0)
    in_L = False
    for x in L:
        if i == x:
            in_L = True
    assert(in_L)

    num = 1
    den = 1
    for j in L:
        if j == i:
            continue
        num = (num * j) % G.order()
        den = (den * (j - i)) % G.order()
    L_i = (num * inverse_mod(den, G.order())) % G.order()
    return L_i

# https://cfrg.github.io/draft-irtf-cfrg-frost/draft-irtf-cfrg-frost.html#name-evaluation-of-a-polynomial
def polynomial_evaluate(G, x, coeffs):
    value = 0
    for coeff in reversed(coeffs):
        value = (value * x) % G.order()
        value = (value + coeff) % G.order()
    return value

# https://cfrg.github.io/draft-irtf-cfrg-frost/draft-irtf-cfrg-frost.html#name-shamir-secret-sharing
def secret_share_combine(G, t, shares):
    def polynomial_interpolation(points):
        L = [x for (x, _) in points]
        constant = 0
        for (x, y) in points:
            delta = (y * derive_lagrange_coefficient(G, x, L)) % G.order()
            constant = (constant + delta) % G.order()
        return constant

    if len(shares) < t:
        raise Exception("invalid parameters")
    s = polynomial_interpolation(shares[:t])
    return s

# https://cfrg.github.io/draft-irtf-cfrg-frost/draft-irtf-cfrg-frost.html#name-shamir-secret-sharing
def secret_share_shard(G, s, n, t):
    if t > n:
        raise Exception("invalid parameters")

    # Generate random coefficients for the polynomial
    coefficients = [s]
    for i in range(t - 1):
        coefficients.append(G.random_scalar())

    # Evaluate the polynomial for each signer, identified by their identifier i > 0
    secret_shares = []
    for x_i in range(1, n+1):
        y_i = polynomial_evaluate(G, x_i, coefficients)
        share_i = (x_i, y_i)
        secret_shares.append(share_i)
    return secret_shares, coefficients

# https://cfrg.github.io/draft-irtf-cfrg-frost/draft-irtf-cfrg-frost.html#name-trusted-dealer-key-generati
def trusted_dealer_keygen(G, secret_key, n, t):
    signer_private_keys, coefficients = secret_share_shard(G, secret_key, n, t)
    vss_commitment = vss_commit(G, coefficients)
    recovered_key = secret_share_combine(G, t, signer_private_keys)
    assert(secret_key == recovered_key)
    return signer_private_keys, vss_commitment

def vss_commit(G, coefficients):
    vss_commitment = []
    for coeff in coefficients:
        comm_i = coeff * G.generator()
        vss_commitment.append(comm_i)
    return vss_commitment

def derive_public_point(G, i, t, vss_commitment):
    public_point = G.identity()
    j = 0
    for comm_j in vss_commitment:
        public_point += comm_j * i**j
        j += 1
    return public_point

def vss_verify(G, share_i, vss_commitment):
    (i, sk_i) = share_i
    SK_i = G.generator() * sk_i
    SK_i_prime = derive_public_point(G, i, len(vss_commitment), vss_commitment)
    return SK_i_prime == SK_i

def derive_group_info(G, n, t, vss_commitment):
    PK = vss_commitment[0]
    signer_public_keys = {}
    for i in range(1, n+1):
        PK_i = derive_public_point(G, i, t, vss_commitment)
        signer_public_keys[i] = PK_i
    return (PK, signer_public_keys)

class Signature(object):
    def __init__(self, G, R, z):
        self.G = G
        self.R = R
        self.z = z

    def encode(self):
        return self.G.serialize(self.R) + self.G.serialize_scalar(self.z)

def encode_group_commitment_list(G, commitment_list):
    B_es = [G.serialize_scalar(i) + G.serialize(D) + G.serialize(E) for (i, D, E) in commitment_list]
    B_e = B_es[0]
    for i, v in enumerate(B_es):
        if i > 0:
            B_e = B_e + v
    return B_e

def compute_binding_factors(G, H, commitment_list, msg):
    msg_hash = H.H4(msg)
    encoded_commitment_hash = H.H5(encode_group_commitment_list(G, commitment_list))
    rho_input_prefix = msg_hash + encoded_commitment_hash

    binding_factors = {}
    rho_inputs = {}
    for _, (i, D, E) in enumerate(commitment_list):
        rho_input = rho_input_prefix + G.serialize_scalar(i)
        binding_factor = H.H1(rho_input)
        rho_inputs[i] = rho_input
        binding_factors[i] = binding_factor
    return binding_factors, rho_inputs

def compute_group_commitment(G, commitment_list, binding_factors):
    group_commitment = G.identity()
    for (i, D_i, E_i) in commitment_list:
        group_commitment = group_commitment + (D_i + (binding_factors[i] * E_i))
    return group_commitment

def compute_challenge(H, group_commitment, group_public_key, msg):
    group_comm_enc = G.serialize(group_commitment)
    group_public_key_enc = G.serialize(group_public_key)
    challenge_input = group_comm_enc + group_public_key_enc + msg
    challenge = H.H2(challenge_input)
    return challenge

def verify_signature_share(G, H, identifier, public_key_share, sig_share, commitment_list, group_public_key, msg):
    # Compute the binding factors
    binding_factors, _ = compute_binding_factors(G, H, commitment_list, msg)
    binding_factor = binding_factors[identifier]

    # Compute the group commitment
    group_commitment = compute_group_commitment(G, commitment_list, binding_factors)

    # Compute the commitment share
    (hiding_nonce_commitment, binding_nonce_commitment) = None, None
    for (i, h, b) in commitment_list:
        if identifier == i:
            hiding_nonce_commitment = h
            binding_nonce_commitment = b
            break
    comm_share = hiding_nonce_commitment + (binding_nonce_commitment * binding_factor)

    # Compute the challenge
    challenge = compute_challenge(H, group_commitment, group_public_key, msg)

    # Compute Lagrange coefficient
    signers = signers_from_commitment_list(commitment_list)
    lambda_i = derive_lagrange_coefficient(G, identifier, signers)

    # Compute relation values
    l = sig_share * G.generator()
    r = comm_share + ((challenge * lambda_i) * public_key_share)

    return l == r

def nonce_generate(H, secret, random_bytes):
    secret_enc = G.serialize_scalar(secret)
    hash_input = random_bytes + secret_enc
    return H.H3(hash_input)

def signers_from_commitment_list(commitment_list):
    return [i for (i, _, _) in commitment_list]

class Signer(object):
    def __init__(self, G, H, sk, pk):
        self.G = G
        self.H = H
        self.identifier = sk[0]
        self.sk = sk[1]
        self.pk = pk

    # https://cfrg.github.io/draft-irtf-cfrg-frost/draft-irtf-cfrg-frost.html#name-round-one
    def commit(self, hiding_nonce_randomness, binding_nonce_randomness):
        hiding_nonce = nonce_generate(self.H, self.sk, hiding_nonce_randomness)
        binding_nonce = nonce_generate(self.H, self.sk, binding_nonce_randomness)
        hiding_nonce_commitment = hiding_nonce * self.G.generator()
        binding_nonce_commitment = binding_nonce * self.G.generator()
        nonce = (hiding_nonce, binding_nonce)
        comm = (hiding_nonce_commitment, binding_nonce_commitment)
        return nonce, comm

    # https://cfrg.github.io/draft-irtf-cfrg-frost/draft-irtf-cfrg-frost.html#name-round-two
    def sign(self, nonce, msg, commitment_list):
        # Compute the binding factors
        binding_factors, _ = compute_binding_factors(self.G, self.H, commitment_list, msg)
        binding_factor = binding_factors[self.identifier]

        # Compute the group commitment
        group_comm = compute_group_commitment(self.G, commitment_list, binding_factors)

        # Compute Lagrange coefficient
        signer_list = signers_from_commitment_list(commitment_list)
        lambda_i = derive_lagrange_coefficient(self.G, self.identifier, signer_list)

        # Compute the per-message challenge
        challenge = compute_challenge(self.H, group_comm, self.pk, msg)

        # Compute the signature share
        (hiding_nonce, binding_nonce) = nonce
        sig_share = hiding_nonce + (binding_nonce * binding_factor) + (lambda_i * self.sk * challenge)
        return sig_share

    # https://cfrg.github.io/draft-irtf-cfrg-frost/draft-irtf-cfrg-frost.html#name-aggregate
    def aggregate(self, group_comm, sig_shares, public_key_shares, commitment_list, msg):
        signer_list = signers_from_commitment_list(commitment_list)
        for identifier in signer_list:
            assert(verify_signature_share(self.G, self.H, identifier, public_key_shares[identifier], sig_shares[identifier], commitment_list, self.pk, msg))

        z = 0
        for z_i in sig_shares.values():
            z = z + z_i

        return Signature(self.G, group_comm, z)

# Configure the setting
MAX_SIGNERS = 3
MIN_SIGNERS = 2
NUM_SIGNERS = MIN_SIGNERS
SIGNER_LIST = [1, 3]
message = _as_bytes("test")

ciphersuites = [
    ("frost-ed25519-sha512", "FROST(Ed25519, SHA-512)", GroupEd25519(), HashEd25519()),
    ("frost-ed448-shake256", "FROST(Ed448, SHAKE256)", GroupEd448(), HashEd448()),
    ("frost-ristretto255-sha512", "FROST(ristretto255, SHA-512)", GroupRistretto255(), HashRistretto255()),
    ("frost-p256-sha256", "FROST(P-256, SHA-256)", GroupP256(), HashP256()),
    ("frost-secp256k1-sha256", "FROST(secp256k1, SHA-256)", GroupSecp256k1(), HashSecp256k1()),
]
for (fname, name, G, H) in ciphersuites:
    assert(MIN_SIGNERS > 1)
    assert(MIN_SIGNERS <= NUM_SIGNERS)
    assert(NUM_SIGNERS <= MAX_SIGNERS)

    config = {}
    config["MAX_SIGNERS"] = str(MAX_SIGNERS)
    config["NUM_SIGNERS"] = str(NUM_SIGNERS)
    config["MIN_SIGNERS"] = str(MIN_SIGNERS)
    config["name"] = name
    config["group"] = G.name
    config["hash"] = H.name

    # Create all inputs, including the group key and individual signer key shares
    group_secret_key = G.random_scalar()
    signer_private_keys, vss_commitment = trusted_dealer_keygen(G, group_secret_key, MAX_SIGNERS, MIN_SIGNERS)
    assert(len(vss_commitment) == MIN_SIGNERS)

    group_public_key, signer_public_keys = derive_group_info(G, MAX_SIGNERS, MIN_SIGNERS, vss_commitment)
    assert(len(signer_public_keys) == MAX_SIGNERS)
    assert(group_public_key == vss_commitment[0])

    for share_i in signer_private_keys:
        assert(vss_verify(G, share_i, vss_commitment))

    group_public_key_enc = G.serialize(group_public_key)
    recovered_group_public_key = G.deserialize(group_public_key_enc)
    assert(group_public_key == recovered_group_public_key)

    # Create signers
    signers = {}
    for _, signer_private_key in enumerate(signer_private_keys):
        identifier = signer_private_key[0]
        signers[identifier] = Signer(G, H, signer_private_key, group_public_key)

    inputs = {
        "group_secret_key": to_hex(G.serialize_scalar(group_secret_key)),
        "group_public_key": to_hex(G.serialize(group_public_key)),
        "message": to_hex(message),
        "signers": {}
    }
    for identifier in signers:
        inputs["signers"][str(identifier)] = {}
        inputs["signers"][str(identifier)]["signer_share"] = to_hex(G.serialize_scalar(signers[identifier].sk))

    # Round one: commitment
    nonces = {}
    comms = {}
    nonce_randomness = {}
    commitment_list = []
    for identifier in PARTICIPANT_LIST:
        hiding_nonce_randomness = random_bytes(32)
        binding_nonce_randomness = random_bytes(32)
        nonce_i, comm_i = signers[identifier].commit(hiding_nonce_randomness, binding_nonce_randomness)
        nonces[identifier] = nonce_i
        comms[identifier] = comm_i
        nonce_randomness[identifier] = (hiding_nonce_randomness, binding_nonce_randomness)
        commitment_list.append((identifier, comm_i[0], comm_i[1]))

    binding_factors, rho_inputs = compute_binding_factors(G, H, commitment_list, message)
    group_commitment = compute_group_commitment(G, commitment_list, binding_factors)

    round_one_outputs = {
        "signer_list": ",".join([str(i) for i in SIGNER_LIST]),
        "signers": {}
    }
    for identifier in SIGNER_LIST:
        round_one_outputs["signers"][str(identifier)] = {}
        round_one_outputs["signers"][str(identifier)]["hiding_nonce_randomness"] = to_hex(nonce_randomness[identifier][0])
        round_one_outputs["signers"][str(identifier)]["binding_nonce_randomness"] = to_hex(nonce_randomness[identifier][1])
        round_one_outputs["signers"][str(identifier)]["hiding_nonce"] = to_hex(G.serialize_scalar(nonces[identifier][0]))
        round_one_outputs["signers"][str(identifier)]["binding_nonce"] = to_hex(G.serialize_scalar(nonces[identifier][1]))
        round_one_outputs["signers"][str(identifier)]["hiding_nonce_commitment"] = to_hex(G.serialize(comms[identifier][0]))
        round_one_outputs["signers"][str(identifier)]["binding_nonce_commitment"] = to_hex(G.serialize(comms[identifier][1]))
        round_one_outputs["signers"][str(identifier)]["binding_factor_input"] = to_hex(rho_inputs[identifier])
        round_one_outputs["signers"][str(identifier)]["binding_factor"] = to_hex(G.serialize_scalar(binding_factors[identifier]))

    # Round two: sign
    sig_shares = {}
    for identifier in SIGNER_LIST:
        sig_share = signers[identifier].sign(nonces[identifier], message, commitment_list)
        sig_shares[identifier] = sig_share

    round_two_outputs = {
        "signer_list": ",".join([str(i) for i in SIGNER_LIST]),
        "signers": {}
    }
    for identifier in SIGNER_LIST:
        round_two_outputs["signers"][str(identifier)] = {}
        round_two_outputs["signers"][str(identifier)]["sig_share"] = to_hex(G.serialize_scalar(sig_shares[identifier]))

    # Final step: aggregate
    sig = signers[1].aggregate(group_commitment, sig_shares, signer_public_keys, commitment_list, message)
    final_output = {
        "sig": to_hex(sig.encode())
    }

    def generate_schnorr_signature(G, H, sk, msg):
        PK = sk * G.generator()
        k = G.random_scalar()
        R = k * G.generator()

        group_comm_enc = G.serialize(R)
        pk_enc = G.serialize(PK)
        challenge_input = bytes(group_comm_enc + pk_enc + msg)
        c = H.H2(challenge_input)

        z = k + (sk * c)
        return Signature(G, R, z)

    def verify_schnorr_signature(G, H, Y, msg, sig):
        R, z = sig.R, sig.z

        comm_enc = G.serialize(R)
        pk_enc = G.serialize(Y)
        challenge_input = bytes(comm_enc + pk_enc + msg)
        c = H.H2(challenge_input)

        l = z * G.generator()
        r = (c * Y) + R
        return l == r

    # Sanity check verification logic
    single_sig = generate_schnorr_signature(G, H, group_secret_key, message)
    assert(verify_schnorr_signature(G, H, group_public_key, message, single_sig))

    if type(G) == type(GroupEd25519()):
        # Sanity check of standard encoding/decoding logic
        import os
        sk = os.urandom(32)
        pk_raw = secret_to_public_raw(sk)
        pk_enc = point_compress(pk_raw)
        pk_enc_dup = G.serialize(G.deserialize(pk_enc))
        assert(pk_enc_dup == pk_enc)

        rfc8032_sig = sig.encode()
        pk_enc = G.serialize(group_public_key)
        pk = G.deserialize(pk_enc)
        assert(pk == group_public_key)
        assert(verify_ed25519_rfc8032(pk_enc, message, rfc8032_sig))

    # Verify the group signature just the same
    assert(verify_schnorr_signature(G, H, group_public_key, message, sig))

    vector = {
        "config": config,
        "inputs": inputs,
        "round_one_outputs": round_one_outputs,
        "round_two_outputs": round_two_outputs,
        "final_output": final_output,
    }
    with open(fname + ".json", "w") as fh:
        fh.write(str(json.dumps(vector, indent=2)))
