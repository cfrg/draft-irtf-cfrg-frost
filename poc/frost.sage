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

class Signature(object):
    def __init__(self, G, R, z):
        self.G = G
        self.R = R
        self.z = z

    def encode(self):
        return self.G.serialize(self.R) + self.G.serialize_scalar(self.z)

class Signer(object):
    def __init__(self, G, H, sk, pk):
        self.G = G
        self.H = H
        self.index = sk[0]
        self.sk = sk[1]
        self.pk = pk

    # https://cfrg.github.io/draft-irtf-cfrg-frost/draft-irtf-cfrg-frost.html#name-round-one
    def commit(self):
        hiding_nonce = self.G.random_scalar()
        binding_nonce = self.G.random_scalar()
        hiding_nonce_commitment = hiding_nonce * self.G.generator()
        binding_nonce_commitment = binding_nonce * self.G.generator()
        nonce = (hiding_nonce, binding_nonce)
        comm = (hiding_nonce_commitment, binding_nonce_commitment)
        return nonce, comm

    def encode_group_commitment_list(self, commitment_list):
        B_es = [I2OSP(i, 2) + self.G.serialize(D) + self.G.serialize(E) for (i, D, E) in commitment_list]
        B_e = B_es[0]
        for i, v in enumerate(B_es):
            if i > 0:
                B_e = B_e + v
        return B_e

    # XXX(caw): break this out into a separate function in the draft?
    def group_commitment(self, commitment_list, binding_factor):
        comm = self.G.identity()
        for (_, D_i, E_i) in commitment_list:
            comm = comm + (D_i + (E_i * binding_factor))

        return comm

    # https://cfrg.github.io/draft-irtf-cfrg-frost/draft-irtf-cfrg-frost.html#name-round-two
    def sign(self, nonce, comm, msg, commitment_list, participant_list):
        msg_hash = self.H.H3(message)
        encoded_comm_list = self.encode_group_commitment_list(commitment_list)
        rho_input = bytes(encoded_comm_list + msg_hash)

        binding_factor = self.H.H1(rho_input)
        group_comm = self.group_commitment(commitment_list, binding_factor)

        group_comm_enc = self.G.serialize(group_comm)
        pk_enc = self.G.serialize(self.pk)
        challenge_input = bytes(group_comm_enc + pk_enc + msg)
        c = self.H.H2(challenge_input)

        L_i = derive_lagrange_coefficient(self.G, self.index, participant_list)

        (d_i, e_i) = nonce
        z_i = d_i + (e_i * binding_factor) + (L_i * self.sk * c)

        (D_i, E_i) = comm
        R_i = D_i + (E_i * binding_factor)

        return z_i, R_i

    # XXX(caw): move this out to a helper function?
    def verify_signature_share(self, group_comm, participant_list, index, group_public_key, public_key_share, sig_share, comm_share, msg):
        group_comm_enc = self.G.serialize(group_comm)
        group_public_key_enc = self.G.serialize(group_public_key)
        challenge_input = bytes(group_comm_enc + group_public_key_enc + msg)
        c = self.H.H2(challenge_input)

        l = sig_share * self.G.generator()

        lambda_i = derive_lagrange_coefficient(self.G, index, participant_list)
        r = comm_share + (public_key_share * c * lambda_i)

        return l == r

    # https://cfrg.github.io/draft-irtf-cfrg-frost/draft-irtf-cfrg-frost.html#name-aggregate
    def aggregate(self, group_comm, sig_shares, participant_list, public_key_shares, comm_shares, msg):
        for index in participant_list:
            assert(self.verify_signature_share(group_comm, participant_list, index, self.pk, public_key_shares[index-1], sig_shares[index-1], comm_shares[index-1], msg))

        z = 0
        for z_i in sig_shares:
            z = z + z_i

        return Signature(self.G, group_comm, z)

# https://cfrg.github.io/draft-irtf-cfrg-frost/draft-irtf-cfrg-frost.html#name-lagrange-coefficients
def derive_lagrange_coefficient(G, i, L):
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
    points = []
    for x_i in range(1, n+1):
        y_i = polynomial_evaluate(G, x_i, coefficients)
        point_i = (x_i, y_i)
        points.append(point_i)
    return points

# https://cfrg.github.io/draft-irtf-cfrg-frost/draft-irtf-cfrg-frost.html#name-trusted-dealer-key-generati
def trusted_dealer_keygen(G, n, t):
    secret_key = G.random_scalar()
    points = secret_share_shard(G, secret_key, n, t)
    recovered_key = secret_share_combine(G, t, points)
    assert(secret_key == recovered_key)
    secret_keys = []
    for i in range(n):
        sk_i = points[i]
        secret_keys.append(sk_i)
    public_key = secret_key * G.generator()
    return secret_keys, secret_key, public_key

# Configure the setting
MAX_SIGNERS = 3
THRESHOLD_LIMIT = 2
NUM_SIGNERS = THRESHOLD_LIMIT
message = _as_bytes("test")

ciphersuites = [
    ("FROST(Ed25519, SHA-512)", GroupEd25519(), HashEd25519()),
    ("FROST(Ed448, SHAKE256)", GroupEd448(), HashEd448()),
    ("FROST(ristretto255, SHA-512)", GroupRistretto255(), HashRistretto255()),
    ("FROST(P-256, SHA-256)", GroupP256(), HashP256()),
]
vectors = {}
for (name, G, H) in ciphersuites:
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
    signer_keys, group_secret_key, group_public_key = trusted_dealer_keygen(G, MAX_SIGNERS, THRESHOLD_LIMIT)

    group_public_key_enc = G.serialize(group_public_key)
    recovered_group_public_key = G.deserialize(group_public_key_enc)
    assert(group_public_key == recovered_group_public_key)

    # Create signers
    signer_public_keys = [sk_i * G.generator() for (_, sk_i) in signer_keys]
    signers = {}
    for index, signer_key in enumerate(signer_keys):
        signers[index+1] = Signer(G, H, signer_key, group_public_key)

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

    group_comm_list = signers[1].encode_group_commitment_list(commitment_list)
    msg_hash = signers[1].H.H3(message)
    rho_input = bytes(group_comm_list + msg_hash)
    binding_factor = signers[1].H.H1(rho_input)
    group_comm = signers[1].group_commitment(commitment_list, binding_factor)

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
    sig_shares = []
    comm_shares = []
    for index in participant_list:
        sig_share, sig_comm = signers[index].sign(nonces[index], comms[index], message, commitment_list, participant_list)
        sig_shares.append(sig_share)
        comm_shares.append(sig_comm)

    round_two_outputs = {
        "participants": ",".join([str(index) for index in participant_list]),
        "signers": {}
    }
    for index in participant_list:
        round_two_outputs["signers"][str(index)] = {}
        round_two_outputs["signers"][str(index)]["sig_share"] = to_hex(G.serialize_scalar(sig_shares[index-1]))
        round_two_outputs["signers"][str(index)]["group_commitment_share"] = to_hex(G.serialize(comm_shares[index-1]))

    # Final set: aggregate
    # XXX(caw): wrap up signature in a data structure with a serialize method
    sig = signers[1].aggregate(group_comm, sig_shares, participant_list, signer_public_keys, comm_shares, message)
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
    vectors[name] = vector

print(json.dumps(vectors, indent=2))
