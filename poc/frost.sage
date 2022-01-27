#!/usr/bin/sage
# vim: syntax=python

import sys

from hash_to_field import I2OSP

try:
    from sagelib.groups import GroupRistretto255, GroupP256
except ImportError as e:
    sys.exit("Error loading preprocessed sage files. Try running `make setup && make clean pyfiles`. Full error: " + e)

_as_bytes = lambda x: x if isinstance(x, bytes) else bytes(x, "utf-8")

class Signer(object):
    def __init__(self, G, sk, pk):
        self.G = G
        # XXX(caw): the draft wraps (index, sk) into the same data structure -- consider doing the same here
        self.index = sk[0]
        self.sk = sk[1]
        self.pk = pk

    def H1(self, x):
        return self.G.hash_to_scalar(x, dst="1")

    def H2(self, x):
        return self.G.hash_to_scalar(x, dst="2")

    # https://cfrg.github.io/draft-irtf-cfrg-frost/draft-irtf-cfrg-frost.html#name-round-one
    def commit(self):
        d = self.G.random_scalar()
        e = self.G.random_scalar()
        D = d * self.G.generator()
        E = e * self.G.generator()
        nonce = (d, e)
        comm = (D, E)
        self.nonce = nonce
        self.comm = comm
        return nonce, comm

    # B={(j, D_j, E_j), ...}
    def encode_group_commitment_shares(self, B):
        # TODO(caw): update based on: https://github.com/cfrg/draft-irtf-cfrg-frost/pull/52
        B_es = [I2OSP(B[i][0], 4) + self.G.serialize(B[i][1]) + self.G.serialize(B[i][2]) for i in range(1, len(B))]
        B_e = B_es[0]
        for i, v in enumerate(B_es):
            if i > 0:
                B_e = B_e + v
        return B_e

    # XXX(caw): break this out into a separate function in the draft?
    def group_commitment(self, B, blinding_factor):
        comm = self.G.identity()
        for (_, D_i, E_i) in B:
            comm = comm + (D_i + (E_i * blinding_factor))

        return comm

    # https://cfrg.github.io/draft-irtf-cfrg-frost/draft-irtf-cfrg-frost.html#name-round-two
    def sign(self, nonce, comm, m, B, L):
        assert(nonce == self.nonce)
        assert(comm == self.comm)

        rho_input = self.encode_group_commitment_shares(B)
        blinding_factor = self.H1(rho_input)
        group_comm = self.group_commitment(B, blinding_factor)

        group_comm_enc = self.G.serialize(group_comm)
        pk_enc = self.G.serialize(self.pk)
        challenge_input = bytes(group_comm_enc + pk_enc + m)
        c = self.H2(challenge_input)

        L_i = derive_lagrange_coefficient(self.G, self.index, L)

        (d_i, e_i) = nonce
        z_i = d_i + (e_i * blinding_factor) + (L_i * self.sk * c)

        (D_i, E_i) = comm
        R_i = D_i + (E_i * blinding_factor)

        return z_i, R_i

    # XXX(caw): move this out to a helper function?
    def verify_share(self, group_comm, participants, index, signer_key, signer_share, signer_comm, message):
        group_comm_enc = self.G.serialize(group_comm)
        pk_enc = self.G.serialize(self.pk)
        challenge_input = bytes(group_comm_enc + pk_enc + message)
        c = self.H2(challenge_input)

        l = signer_share * self.G.generator()

        lambda_i = derive_lagrange_coefficient(self.G, index, participants)
        r = signer_comm + (signer_key * c * lambda_i) 

        return l == r

    # https://cfrg.github.io/draft-irtf-cfrg-frost/draft-irtf-cfrg-frost.html#name-aggregate
    def aggregate(self, group_comm, sig_shares, participants, signer_keys, signer_comms, message):
        for index in participants:
            assert(self.verify_share(group_comm, participants, index, signer_keys[index-1], sig_shares[index-1], signer_comms[index-1], message))

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

n = 3 # number of participants
t = 2 # threshold
assert(t > 1)
G = GroupRistretto255()

# Create all signer keys with the trusted dealer and then instantiate each Signer
signer_keys, group_secret_key, group_public_key = trusted_dealer_keygen(G, n, t)
signer_public_keys = [sk_i * G.generator() for (_, sk_i) in signer_keys]
signers = {}
for index, signer_key in enumerate(signer_keys):
    signers[index+1] = Signer(G, signer_key, group_public_key)

# Round one: commitment
nonces = {}
comms = {} 
B = [] # XXX(caw): need a better name for this structure
participants = [i+1 for i in range(t)]
for index in participants:
    nonce_i, comm_i = signers[index].commit()
    nonces[index] = nonce_i
    comms[index] = comm_i
    B.append((index, comm_i[0], comm_i[1]))

# XXX(caw): should this go into round one or two?
rho_input = signers[1].encode_group_commitment_shares(B)
blinding_factor = signers[1].H1(rho_input)
group_comm = signers[1].group_commitment(B, blinding_factor)

# Round two: sign
message = _as_bytes("test")
sig_shares = []
sig_comms = []
for index in participants:
    sig_share, sig_comm = signers[index].sign(nonces[index], comms[index], message, B, participants)
    sig_shares.append(sig_share)
    sig_comms.append(sig_comm)

# Final set: aggregate
sig = signers[1].aggregate(group_comm, sig_shares, participants, signer_public_keys, sig_comms, message)

def generate_schnorr_signature(G, s, m):
    pk = s * G.generator()
    k = G.random_scalar()
    R = k * G.generator()
    group_comm_enc = G.serialize(R)
    pk_enc = G.serialize(pk)
    challenge_input = bytes(group_comm_enc + pk_enc + m)
    c = G.hash_to_scalar(challenge_input, dst="2") # XXX(caw): replace with H2
    z = k + (s * c)
    return (R, z)

def verify_schnorr_signature(G, Y, m, SIG):
    (R, z) = SIG

    comm_enc = G.serialize(R)
    pk_enc = G.serialize(Y)
    challenge_input = bytes(comm_enc + pk_enc + m)
    c = G.hash_to_scalar(challenge_input, dst="2") # XXX(caw): replace with H2

    R_prime = (z * G.generator()) + (Y * -c)
    return R == R_prime

# Sanity check verification logic
single_sig = generate_schnorr_signature(G, group_secret_key, message)
assert(verify_schnorr_signature(G, group_public_key, message, single_sig))

# Verify the group signature just the same
assert(verify_schnorr_signature(G, group_public_key, message, sig))