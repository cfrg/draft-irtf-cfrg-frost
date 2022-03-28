#!/usr/bin/sage
# vim: syntax=python

import sys
import json

from hash_to_field import I2OSP
from ed25519_rfc8032 import verify_ed25519_rfc8032, point_compress, secret_to_public_raw

try:
    from sagelib.groups import GroupRistretto255, GroupEd25519, GroupEd448, GroupP256
    from sagelib.hash import HashEd25519, HashEd448, HashRistretto255, HashP256
except ImportError as e:
    sys.exit("Error loading preprocessed sage files. Try running `make setup && make clean pyfiles`. Full error: " + e)

_as_bytes = lambda x: x if isinstance(x, bytes) else bytes(x, "utf-8")

def to_hex(octet_string):
    if isinstance(octet_string, str):
        return "".join("{:02x}".format(ord(c)) for c in octet_string)
    if isinstance(octet_string, bytes):
        return "" + "".join("{:02x}".format(c) for c in octet_string)
    assert isinstance(octet_string, bytearray)
    return ''.join(format(x, '02x') for x in octet_string)

# https://cfrg.github.io/draft-irtf-cfrg-frost/draft-irtf-cfrg-frost.html#name-lagrange-coefficients
def derive_lagrange_coefficient(G, i, L):
    assert(i != 0)
    for j in L:
      assert(j != 0)

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
    for i, coeff in enumerate(reversed(coeffs)):
        if i == (len(coeffs) - 1):
            value = (value + coeff) % G.order()
        else:
            value = (value + coeff) % G.order()
            value = (value * x) % G.order()
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

    # Evaluate the polynomial for each participant, identified by their index i > 0
    secret_shares = []
    for x_i in range(1, n+1):
        y_i = polynomial_evaluate(G, x_i, coefficients)
        share_i = (x_i, y_i)
        secret_shares.append(share_i)
    return secret_shares, coefficients

# https://cfrg.github.io/draft-irtf-cfrg-frost/draft-irtf-cfrg-frost.html#name-trusted-dealer-key-generati
def trusted_dealer_keygen(G, secret_key, n, t):
    secret_shares, coefficients = secret_share_shard(G, secret_key, n, t)
    vss_commitment = vss_commit(G, coefficients)
    recovered_key = secret_share_combine(G, t, secret_shares)
    assert(secret_key == recovered_key)
    secret_keys = []
    for i in range(n):
        sk_i = secret_shares[i]
        secret_keys.append(sk_i)
    public_key = secret_key * G.generator()
    return secret_keys, public_key, vss_commitment

def vss_commit(G, coefficients):
  vss_commitment = []
  for coeff in coefficients:
    comm_i = coeff * G.generator()
    vss_commitment.append(comm_i)
  return vss_commitment

def vss_verify(G, share_i, vss_commitment):
  (i, sk_i) = share_i
  SK_i = G.generator() * sk_i
  SK_i_prime = G.identity()
  j = 0
  for comm_j in vss_commitment:
    SK_i_prime += comm_j * i**j
    j += 1
  return SK_i_prime == SK_i

class Signature(object):
    def __init__(self, G, R, z):
        self.G = G
        self.R = R
        self.z = z

    def encode(self):
        return self.G.serialize(self.R) + self.G.serialize_scalar(self.z)

def encode_group_commitment_list(G, commitment_list):
    B_es = [I2OSP(i, 2) + G.serialize(D) + G.serialize(E) for (i, D, E) in commitment_list]
    B_e = B_es[0]
    for i, v in enumerate(B_es):
        if i > 0:
            B_e = B_e + v
    return B_e

def compute_binding_factor(H, encoded_commitments, msg):
    msg_hash = H.H3(msg)
    rho_input = encoded_commitments + msg_hash
    binding_factor = H.H1(rho_input)
    return binding_factor, rho_input

def compute_group_commitment(G, commitment_list, binding_factor):
    group_commitment = G.identity()
    for (_, D_i, E_i) in commitment_list:
        group_commitment = group_commitment + (D_i + (E_i * binding_factor))
    return group_commitment

def compute_challenge(H, group_commitment, group_public_key, msg):
    group_comm_enc = G.serialize(group_commitment)
    group_public_key_enc = G.serialize(group_public_key)
    challenge_input = group_comm_enc + group_public_key_enc + msg
    challenge = H.H2(challenge_input)
    return challenge

def verify_signature_share(G, H, index, public_key_share, comm, sig_share, commitment_list, participant_list, group_public_key, msg):
    # Encode the commitment list
    encoded_commitments = encode_group_commitment_list(G, commitment_list)

    # Compute the binding factor
    binding_factor, _ = compute_binding_factor(H, encoded_commitments, msg)

    # Compute the group commitment
    group_commitment = compute_group_commitment(G, commitment_list, binding_factor)

    # Compute the commitment share
    (hiding_nonce_commitment, binding_nonce_commitment) = comm
    comm_share = hiding_nonce_commitment + (binding_nonce_commitment * binding_factor)

    # Compute the challenge
    challenge = compute_challenge(H, group_commitment, group_public_key, msg)

    # Compute Lagrange coefficient
    lambda_i = derive_lagrange_coefficient(G, index, participant_list)

    # Compute relation values
    l = sig_share * G.generator()
    r = comm_share + (public_key_share * challenge * lambda_i)

    return l == r

class Signer(object):
    def __init__(self, G, H, sk, pk):
        self.G = G
        self.H = H
        self.index = sk[0]
        self.sk = sk[1]
        self.pk = pk

    # https://cfrg.github.io/draft-irtf-cfrg-frost/draft-irtf-cfrg-frost.html#name-round-one
    def commit(self):
        hiding_nonce = self.G.random_nonzero_scalar()
        binding_nonce = self.G.random_nonzero_scalar()
        hiding_nonce_commitment = hiding_nonce * self.G.generator()
        binding_nonce_commitment = binding_nonce * self.G.generator()
        nonce = (hiding_nonce, binding_nonce)
        comm = (hiding_nonce_commitment, binding_nonce_commitment)
        return nonce, comm

    # https://cfrg.github.io/draft-irtf-cfrg-frost/draft-irtf-cfrg-frost.html#name-round-two
    def sign(self, nonce, msg, commitment_list, participant_list):
        # Encode the commitment list
        encoded_commitments = encode_group_commitment_list(self.G, commitment_list)

        # Compute the binding factor
        binding_factor, _ = compute_binding_factor(self.H, encoded_commitments, msg)

        # Compute the group commitment
        group_comm = compute_group_commitment(self.G, commitment_list, binding_factor)

        # Compute Lagrange coefficient
        lambda_i = derive_lagrange_coefficient(self.G, self.index, participant_list)

        # Compute the per-message challenge
        challenge = compute_challenge(self.H, group_comm, self.pk, msg)

        # Compute the signature share
        (hiding_nonce, binding_nonce) = nonce
        sig_share = hiding_nonce + (binding_nonce * binding_factor) + (lambda_i * self.sk * challenge)
        return sig_share

    # https://cfrg.github.io/draft-irtf-cfrg-frost/draft-irtf-cfrg-frost.html#name-aggregate
    def aggregate(self, group_comm, sig_shares, participant_list, public_key_shares, comm_list, msg):
        for index in participant_list:
            assert(verify_signature_share(self.G, self.H, index, public_key_shares[index], comm_list[index], sig_shares[index], commitment_list, participant_list, self.pk, msg))

        z = 0
        for z_i in sig_shares.values():
            z = z + z_i

        return Signature(self.G, group_comm, z)

# Configure the setting
MAX_SIGNERS = 3
THRESHOLD_LIMIT = 2
NUM_SIGNERS = THRESHOLD_LIMIT
message = _as_bytes("test")

ciphersuites = [
    ("frost-ed25519-sha512", "FROST(Ed25519, SHA-512)", GroupEd25519(), HashEd25519()),
    ("frost-ed448-shake256", "FROST(Ed448, SHAKE256)", GroupEd448(), HashEd448()),
    ("frost-ristretto255-sha512", "FROST(ristretto255, SHA-512)", GroupRistretto255(), HashRistretto255()),
    ("frost-p256-sha256", "FROST(P-256, SHA-256)", GroupP256(), HashP256()),
]
for (fname, name, G, H) in ciphersuites:
    participant_list = [i+1 for i in range(NUM_SIGNERS)]

    assert(THRESHOLD_LIMIT > 1)
    assert(THRESHOLD_LIMIT <= NUM_SIGNERS)
    assert(NUM_SIGNERS <= MAX_SIGNERS)

    config = {}
    config["MAX_SIGNERS"] = str(MAX_SIGNERS)
    config["NUM_SIGNERS"] = str(NUM_SIGNERS)
    config["THRESHOLD_LIMIT"] = str(THRESHOLD_LIMIT)
    config["name"] = name
    config["group"] = G.name
    config["hash"] = H.name

    # Create all inputs, including the group key and individual signer key shares
    group_secret_key = G.random_scalar()
    signer_keys, group_public_key, vss_commitment = trusted_dealer_keygen(G, group_secret_key, MAX_SIGNERS, THRESHOLD_LIMIT)
    assert(len(vss_commitment) == THRESHOLD_LIMIT)

    for share_i in signer_keys:
      assert(vss_verify(G, share_i, vss_commitment))

    group_public_key_enc = G.serialize(group_public_key)
    recovered_group_public_key = G.deserialize(group_public_key_enc)
    assert(group_public_key == recovered_group_public_key)

    # Create signers
    signer_public_keys = {}
    signers = {}
    for index, signer_key in enumerate(signer_keys):
        signers[index+1] = Signer(G, H, signer_key, group_public_key)
        signer_public_keys[index+1] = signer_key[1] * G.generator()

    inputs = {
        "group_secret_key": to_hex(G.serialize_scalar(group_secret_key)),
        "group_public_key": to_hex(G.serialize(group_public_key)),
        "message": to_hex(message),
        "signers": {}
    }
    for index in signers:
        inputs["signers"][str(index)] = {}
        inputs["signers"][str(index)]["signer_share"] = to_hex(G.serialize_scalar(signers[index].sk))

    # Round one: commitment
    # XXX(caw): wrap up nonces and commitments in a data structure
    nonces = {}
    comms = {}
    commitment_list = [] # XXX(caw): need a better name for this structure
    for index in participant_list:
        nonce_i, comm_i = signers[index].commit()
        nonces[index] = nonce_i
        comms[index] = comm_i
        commitment_list.append((index, comm_i[0], comm_i[1]))

    encoded_commitments = encode_group_commitment_list(G, commitment_list)
    binding_factor, rho_input = compute_binding_factor(H, encoded_commitments, message)
    group_comm = compute_group_commitment(G, commitment_list, binding_factor)

    round_one_outputs = {
        "participants": ",".join([str(index) for index in participant_list]),
        "group_binding_factor_input": to_hex(rho_input),
        "group_binding_factor": to_hex(G.serialize_scalar(binding_factor)),
        "signers": {}
    }
    for index in participant_list:
        round_one_outputs["signers"][str(index)] = {}
        round_one_outputs["signers"][str(index)]["hiding_nonce"] = to_hex(G.serialize_scalar(nonces[index][0]))
        round_one_outputs["signers"][str(index)]["binding_nonce"] = to_hex(G.serialize_scalar(nonces[index][1]))
        round_one_outputs["signers"][str(index)]["hiding_nonce_commitment"] = to_hex(G.serialize(comms[index][0]))
        round_one_outputs["signers"][str(index)]["binding_nonce_commitment"] = to_hex(G.serialize(comms[index][1]))

    # Round two: sign
    sig_shares = {}
    for index in participant_list:
        sig_share = signers[index].sign(nonces[index], message, commitment_list, participant_list)
        sig_shares[index] = sig_share

    round_two_outputs = {
        "participants": ",".join([str(index) for index in participant_list]),
        "signers": {}
    }
    for index in participant_list:
        round_two_outputs["signers"][str(index)] = {}
        round_two_outputs["signers"][str(index)]["sig_share"] = to_hex(G.serialize_scalar(sig_shares[index]))

    # Final step: aggregate
    sig = signers[1].aggregate(group_comm, sig_shares, participant_list, signer_public_keys, comms, message)
    final_output = {
        "sig": to_hex(sig.encode())
    }

    def generate_schnorr_signature(G, H, s, msg):
        pk = s * G.generator()
        k = G.random_scalar()
        R = k * G.generator()

        group_comm_enc = G.serialize(R)
        pk_enc = G.serialize(pk)
        challenge_input = bytes(group_comm_enc + pk_enc + msg)
        c = H.H2(challenge_input)

        z = k + (s * c)
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
        pkk = G.serialize(G.deserialize(pk_enc))
        assert(pkk == pk_enc)

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
    # vectors[name] = vector
    with open(fname + ".json", "w") as fh:
        fh.write(str(json.dumps(vector, indent=2)))
