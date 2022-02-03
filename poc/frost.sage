#!/usr/bin/sage
# vim: syntax=python

import sys
import json

from hashlib import sha512, sha256
from hash_to_field import I2OSP
from ed25519_rfc8032 import verify_ed25519_rfc8032, point_compress, secret_to_public_raw

try:
    from sagelib.groups import GroupRistretto255, GroupEd25519, GroupP256
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

class Signer(object):
    def __init__(self, G, H, sk, pk):
        self.G = G
        self.H = H
        self.index = sk[0]
        self.sk = sk[1]
        self.pk = pk

    def H1(self, x):
        '''
        H1(m) = H(contextString || "rho" || I2OSP(len(m), 8) || m)
        '''
        return self.G.hash_to_scalar(x, dst="1")

    def H2(self, x):
        '''
        H2(m) = H(contextString || "chal" || I2OSP(len(m), 8) || m)
        '''
        return self.G.hash_to_scalar(x, dst="2")

    def H3(self, x):
        '''
        H3(m) = H(m)
        '''
        hasher = self.H()
        hasher.update(x)
        return hasher.digest()

    # https://cfrg.github.io/draft-irtf-cfrg-frost/draft-irtf-cfrg-frost.html#name-round-one
    def commit(self):
        d = self.G.random_scalar()
        e = self.G.random_scalar()
        D = d * self.G.generator()
        E = e * self.G.generator()
        nonce = (d, e)
        comm = (D, E)
        return nonce, comm

    def encode_group_commitment_list(self, commitment_list):
        B_es = [I2OSP(i, 2) + self.G.serialize(D) + self.G.serialize(E) for (i, D, E) in commitment_list]
        B_e = B_es[0]
        for i, v in enumerate(B_es):
            if i > 0:
                B_e = B_e + v
        return B_e

    # XXX(caw): break this out into a separate function in the draft?
    def group_commitment(self, commitment_list, blinding_factor):
        comm = self.G.identity()
        for (_, D_i, E_i) in commitment_list:
            comm = comm + (D_i + (E_i * blinding_factor))

        return comm

    # https://cfrg.github.io/draft-irtf-cfrg-frost/draft-irtf-cfrg-frost.html#name-round-two
    def sign(self, nonce, comm, msg, commitment_list, participant_list):
        msg_hash = self.H3(message)
        encoded_comm_list = self.encode_group_commitment_list(commitment_list)
        rho_input = bytes(encoded_comm_list + msg_hash)

        blinding_factor = self.H1(rho_input)
        group_comm = self.group_commitment(commitment_list, blinding_factor)

        group_comm_enc = self.G.serialize(group_comm)
        pk_enc = self.G.serialize(self.pk)
        challenge_input = bytes(group_comm_enc + pk_enc + msg)
        c = self.H2(challenge_input)

        L_i = derive_lagrange_coefficient(self.G, self.index, participant_list)

        (d_i, e_i) = nonce
        z_i = d_i + (e_i * blinding_factor) + (L_i * self.sk * c)

        (D_i, E_i) = comm
        R_i = D_i + (E_i * blinding_factor)

        return z_i, R_i

    # XXX(caw): move this out to a helper function?
    def verify_share(self, group_comm, participant_list, index, signer_key, signer_share, signer_comm, msg):
        group_comm_enc = self.G.serialize(group_comm)
        pk_enc = self.G.serialize(self.pk)
        challenge_input = bytes(group_comm_enc + pk_enc + msg)
        c = self.H2(challenge_input)

        l = signer_share * self.G.generator()

        lambda_i = derive_lagrange_coefficient(self.G, index, participant_list)
        r = signer_comm + (signer_key * c * lambda_i)

        return l == r

    # https://cfrg.github.io/draft-irtf-cfrg-frost/draft-irtf-cfrg-frost.html#name-aggregate
    def aggregate(self, group_comm, sig_shares, participant_list, signer_keys, signer_comms, msg):
        for index in participant_list:
            assert(self.verify_share(group_comm, participant_list, index, signer_keys[index-1], sig_shares[index-1], signer_comms[index-1], msg))

        z = 0
        for z_i in sig_shares:
            z = z + z_i

        return (group_comm, z)

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
def secret_share_split(G, s, n, t):
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
    points = secret_share_split(G, secret_key, n, t)
    recovered_key = secret_share_combine(G, t, points)
    assert(secret_key == recovered_key)
    secret_keys = []
    for i in range(n):
        sk_i = points[i]
        secret_keys.append(sk_i)
    public_key = secret_key * G.generator()
    return secret_keys, secret_key, public_key

# Configure the setting
NUM_SIGNERS = 3
THRESHOLD_LIMIT = 2
message = _as_bytes("test")

ciphersuites = [
    ("FROST(Ed25519, SHA512)", GroupEd25519(), sha512), 
    ("FROST(ristretto255, SHA512)", GroupRistretto255(), sha512), 
    ("FROST(P-256, SHA256)", GroupP256(), sha256),
]
vectors = {}
for (name, G, H) in ciphersuites:
    participant_list = [i+1 for i in range(THRESHOLD_LIMIT)]

    assert(THRESHOLD_LIMIT > 1)
    assert(THRESHOLD_LIMIT <= NUM_SIGNERS)

    config = {}
    config["NUM_SIGNERS"] = str(NUM_SIGNERS)
    config["THRESHOLD_LIMIT"] = str(THRESHOLD_LIMIT)
    config["name"] = name
    config["group"] = G.name
    config["hash"] = H().name.upper()

    # Create all inputs, including the group key and individual signer key shares
    signer_keys, group_secret_key, group_public_key = trusted_dealer_keygen(G, NUM_SIGNERS, THRESHOLD_LIMIT)
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
    msg_hash = signers[1].H3(message)
    rho_input = bytes(group_comm_list + msg_hash)

    blinding_factor = signers[1].H1(rho_input)
    group_comm = signers[1].group_commitment(commitment_list, blinding_factor)

    round_one_outputs = {
        "participants": [str(index) for index in participant_list],
        "commitment_list": to_hex(rho_input),
        "group_blinding_factor": to_hex(G.serialize_scalar(blinding_factor)),
        "outputs": {}
    }
    for index in participant_list:
        round_one_outputs["outputs"][str(index)] = {}
        round_one_outputs["outputs"][str(index)]["hiding_nonce"] = to_hex(G.serialize_scalar(nonces[index][0]))
        round_one_outputs["outputs"][str(index)]["blinding_nonce"] = to_hex(G.serialize_scalar(nonces[index][1]))
        round_one_outputs["outputs"][str(index)]["hiding_nonce_commitment"] = to_hex(G.serialize(comms[index][0]))
        round_one_outputs["outputs"][str(index)]["blinding_nonce_commitment"] = to_hex(G.serialize(comms[index][1]))

    # Round two: sign
    sig_shares = []
    comm_shares = []
    for index in participant_list:
        sig_share, sig_comm = signers[index].sign(nonces[index], comms[index], message, commitment_list, participant_list)
        sig_shares.append(sig_share)
        comm_shares.append(sig_comm)

    round_two_outputs = {
        "participants": [str(index) for index in participant_list],
        "outputs": {}
    }
    for index in participant_list:
        round_two_outputs["outputs"][str(index)] = {}
        round_two_outputs["outputs"][str(index)]["sig_share"] = to_hex(G.serialize_scalar(sig_shares[index-1]))
        round_two_outputs["outputs"][str(index)]["group_commitment_share"] = to_hex(G.serialize(comm_shares[index-1]))

    # Final set: aggregate
    # XXX(caw): wrap up signature in a data structure with a serialize method
    sig = signers[1].aggregate(group_comm, sig_shares, participant_list, signer_public_keys, comm_shares, message)
    final_output = {
        "sig": {}
    }
    final_output["sig"]["R"] = to_hex(G.serialize(sig[0]))
    final_output["sig"]["z"] = to_hex(G.serialize_scalar(sig[1]))

    def generate_schnorr_signature(G, s, msg):
        pk = s * G.generator()
        k = G.random_scalar()
        R = k * G.generator()

        group_comm_enc = G.serialize(R)
        pk_enc = G.serialize(pk)
        challenge_input = bytes(group_comm_enc + pk_enc + msg)
        c = G.hash_to_scalar(challenge_input, dst="2") # XXX(caw): replace with H2

        z = k + (s * c)
        return (R, z)

    def verify_schnorr_signature(G, Y, msg, SIG):
        (R, z) = SIG

        comm_enc = G.serialize(R)
        pk_enc = G.serialize(Y)
        challenge_input = bytes(comm_enc + pk_enc + msg)
        c = G.hash_to_scalar(challenge_input, dst="2") # XXX(caw): replace with H2

        l = z * G.generator()
        r = (c * Y) + R
        return l == r

    # Sanity check verification logic
    single_sig = generate_schnorr_signature(G, group_secret_key, message)
    assert(verify_schnorr_signature(G, group_public_key, message, single_sig))

    if type(G) == type(GroupEd25519()):
        # Sanity check of standard encoding/decoding logic
        import os
        sk = os.urandom(32)
        pk_raw = secret_to_public_raw(sk)
        pk_enc = point_compress(pk_raw)
        pkk = G.serialize(G.deserialize(pk_enc))
        assert(pkk == pk_enc)

        rfc8032_sig = G.serialize(single_sig[0]) + G.serialize_scalar(single_sig[1]) # Transform into RFC8032-style signature
        pk_enc = G.serialize(group_public_key)
        pk = G.deserialize(pk_enc)
        assert(pk == group_public_key)
        assert(verify_ed25519_rfc8032(pk_enc, message, rfc8032_sig))

    # Verify the group signature just the same
    assert(verify_schnorr_signature(G, group_public_key, message, sig))

    vector = {
        "config": config,
        "inputs": inputs,
        "round_one_outputs": round_one_outputs,
        "round_two_outputs": round_two_outputs,
        "final_output": final_output,
    }
    vectors[name] = vector

print(json.dumps(vectors, indent=2))
