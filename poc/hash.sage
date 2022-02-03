#!/usr/bin/sage
# vim: syntax=python

import sys

from hashlib import sha512, sha256

try:
    from sagelib.groups import GroupRistretto255, GroupEd25519, GroupP256
except ImportError as e:
    sys.exit("Error loading preprocessed sage files. Try running `make setup && make clean pyfiles`. Full error: " + e)

_as_bytes = lambda x: x if isinstance(x, bytes) else bytes(x, "utf-8")

class Hash(object):
    def __init__(self, G, H, name):
        self.G = G
        self.H = H
        self.name = name

    def H1(self, m):
        raise Exception("Not implemented")

    def H2(self, m):
        raise Exception("Not implemented")

    def H3(self, m):
        '''
        H3(m) = H(m)
        '''
        hasher = self.H()
        hasher.update(m)
        return hasher.digest()

class HashEd25519(Hash):
    def __init__(self):
        Hash.__init__(self, GroupEd25519(), sha512, "SHA-512")

    def H1(self, m):
        hash_input = _as_bytes("rho") + m
        return int.from_bytes(sha512(hash_input).digest(), "little") % self.G.order()

    def H2(self, m):
        return int.from_bytes(sha512(m).digest(), "little") % self.G.order()

class HashRistretto255(Hash):
    def __init__(self):
        Hash.__init__(self, GroupRistretto255(), sha512, "SHA-512")

    def H1(self, m):
        hash_input = _as_bytes("FROST-RISTRETTO255-SHA512 rho") + m
        return int.from_bytes(sha512(hash_input).digest(), "little") % self.G.order()

    def H2(self, m):
        hash_input = _as_bytes("FROST-RISTRETTO255-SHA512 chal") + m
        return int.from_bytes(sha512(hash_input).digest(), "little") % self.G.order()

class HashP256(Hash):
    def __init__(self):
        Hash.__init__(self, GroupP256(), sha256, "SHA-256")

    def H1(self, m):
        dst = _as_bytes("FROST-P256-SHA256 rho")
        return self.G.hash_to_scalar(m, dst=dst)

    def H2(self, m):
        dst = _as_bytes("FROST-P256-SHA256 chal")
        return self.G.hash_to_scalar(m, dst=dst)