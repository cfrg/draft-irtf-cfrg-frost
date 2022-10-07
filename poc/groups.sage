#!/usr/bin/sage
# vim: syntax=python

import sys
import random
import hashlib

from hash_to_field import I2OSP, OS2IP, expand_message_xmd, hash_to_field

try:
    from sagelib.common import sgn0
    from sagelib.ristretto_decaf import Ed25519Point, Ed448GoldilocksPoint
except ImportError as e:
    sys.exit("Error loading preprocessed sage files. Try running `make setup && make clean pyfiles`. Full error: " + e)

if sys.version_info[0] == 3:
    xrange = range
    _as_bytes = lambda x: x if isinstance(x, bytes) else bytes(x, "utf-8")
    _strxor = lambda str1, str2: bytes( s1 ^ s2 for (s1, s2) in zip(str1, str2) )
else:
    _as_bytes = lambda x: x
    _strxor = lambda str1, str2: ''.join( chr(ord(s1) ^ ord(s2)) for (s1, s2) in zip(str1, str2) )

# Fix a seed so all test vectors are deterministic
FIXED_SEED = "test".encode('utf-8')
random.seed(int.from_bytes(hashlib.sha256(FIXED_SEED).digest(), 'big'))

class Group(object):
    def __init__(self, name):
        self.name = name

    def generator(self):
        raise Exception("not implemented")

    def identity(self):
        raise Exception("not implemented")

    def order(self):
        raise Exception("not implemented")

    def serialize(self, element):
        raise Exception("not implemented")

    def deserialize(self, encoded):
        raise Exception("not implemented")

    def serialize_scalar(self, scalar):
        raise Exception("not implemented")

    def element_byte_length(self):
        raise Exception("not implemented")

    def scalar_byte_length(self):
        raise Exception("not implemented")

    def hash_to_scalar(self, x):
        raise Exception("not implemented")

    def random_scalar(self):
        return random.randint(0, self.order() - 1)

    def random_nonzero_scalar(self):
        return random.randint(1, self.order() - 1)

    def __str__(self):
        return self.name

class GroupNISTCurve(Group):
    def __init__(self, name, F, A, B, p, order, gx, gy, L, H, expand, k):
        Group.__init__(self, name)
        self.F = F
        EC = EllipticCurve(F, [F(A), F(B)])
        self.curve = EC
        self.gx = gx
        self.gy = gy
        self.p = p
        self.a = A
        self.b = B
        self.group_order = order
        self.G = EC(F(gx), F(gy))
        self.m = F.degree()
        self.L = L
        self.k = k
        self.H = H
        self.expand = expand
        self.field_bytes_length = int(ceil(len(self.p.bits()) / 8))

    def generator(self):
        return self.G

    def order(self):
        return self.group_order

    def identity(self):
        return self.curve(0)

    def serialize(self, element):
        if element == self.identity():
            raise Exception("Identity element not permitted")

        x, y = element[0], element[1]
        sgn = sgn0(y)
        byte = 2 if sgn == 0 else 3
        return I2OSP(byte, 1) + I2OSP(x, self.field_bytes_length)

    # this is using point compression
    def deserialize(self, encoded):
        # 0x02 | 0x03 || x
        pve = encoded[0] == 0x02
        nve = encoded[0] == 0x03
        assert(pve or nve)
        assert(len(encoded) % 2 != 0)
        x = OS2IP(encoded[1:])
        y2 = x^3 + self.a*x + self.b
        y = y2.sqrt()
        parity = 0 if pve else 1
        if sgn0(y) != parity:
            y = -y
        point = self.curve(self.F(x), self.F(y))

        if point == self.identity():
            raise Exception("Identity element not permitted")

        return point

    def serialize_scalar(self, scalar):
        return I2OSP(scalar % self.order(), self.scalar_byte_length())

    def element_byte_length(self):
        return int(1 + self.field_bytes_length)

    def scalar_byte_length(self):
        return int(self.field_bytes_length)

    def hash_to_scalar(self, msg, dst=""):
        return hash_to_field(msg, 1, dst, self.order(), self.m, self.L, self.expand, self.H, self.k)[0][0]


class GroupP256(GroupNISTCurve):
    def __init__(self):
        # See FIPS 186-3, section D.2.3
        p = 2^256 - 2^224 + 2^192 + 2^96 - 1
        F = GF(p)
        A = F(-3)
        B = F(0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b)
        order = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
        gx = 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296
        gy = 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5
        GroupNISTCurve.__init__(self, "P-256", F, A, B, p, order, gx, gy, 48, hashlib.sha256, expand_message_xmd, 128)

# Marker to denote the origin of the curve, relying on the coinciding specs
class GroupSECGCurve(GroupNISTCurve):
  pass

class GroupSecp256k1(GroupSECGCurve):
    def __init__(self):
        # See SEC 2 v2, section 2.4.1
        p = 2^256 - 2^32 - 2^9 - 2^8 - 2^7 - 2^6 - 2^4 - 1
        F = GF(p)
        A = F(0)
        B = F(7)
        order = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141
        gx = 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798
        gy = 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8
        GroupSECGCurve.__init__(self, "secp256k1", F, A, B, p, order, gx, gy, 48, hashlib.sha256, expand_message_xmd, 128)

class GroupEd25519(Group):
    # Compute corresponding x-coordinate, with low bit corresponding to
    # sign, or return None on failure
    def recover_x(y, sign, p, d):
        def modp_inv(x):
            return pow(x, p-2, p)
        if y >= p:
            return None
        x2 = (y^2-1) * modp_inv(d*y^2+1)
        if x2 == 0:
            if sign:
                return None
            else:
                return 0

        # Compute square root of x2
        x = int(pow(x2, (p+3) // 8, p))
        if (x*x - x2) % p != 0:
            modp_sqrt_m1 = pow(2, (p-1) // 4, p)
            x = int(x * modp_sqrt_m1 % p)
        if (x*x - x2) % p != 0:
            return None

        if (x & 1) != sign:
            x = p - x
        return x

    def to_weierstrass(a, d, x, y):
        return ((5*a + a*y - 5*d*y - d)/(12 - 12*y), (a + a*y - d*y -d)/(4*x - 4*x*y))

    def to_twistededwards(a, d, u, v):
        y = (5*a - 12*u - d)/(-12*u - a + 5*d)
        x = (a + a*y - d*y -d)/(4*v - 4*v*y)
        return (x, y)

    def __init__(self):
        Group.__init__(self, "ed25519")
        # Borrowed from: https://neuromancer.sk/std/other/Ed25519
        p = 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed
        K = GF(p)
        a = K(0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffec)
        d = 0x52036cee2b6ffe738cc740797779e89800700a4d4141d8ab75eb4dca135978a3
        E = EllipticCurve(K, (K(-1/48) * (a^2 + 14*a*d + d^2),K(1/864) * (a + d) * (-a^2 + 34*a*d - d^2)))
        G = E(*GroupEd25519.to_weierstrass(a, K(d), K(0x216936D3CD6E53FEC0A4E231FDD6DC5C692CC7609525A7B2C9562D608F25D51A), K(0x6666666666666666666666666666666666666666666666666666666666666658)))
        order = 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed * 0x08
        E.set_order(order)

        self.F = K
        self.curve = E
        self.p = p
        self.group_order = 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed
        self.G = G
        self.a = a
        self.d = d

    def generator(self):
        return self.G

    def order(self):
        return self.group_order

    def identity(self):
        return self.curve(0)

    def serialize(self, element):
        if element == self.identity():
            raise Exception("Identity element not permitted")

        (x, y) = element.xy()
        (u, v) = GroupEd25519.to_twistededwards(self.a, self.d, x, y)

        sign = int(int(u) % 2)
        return int.to_bytes(int(v) | (sign << 255), 32, "little")

    def deserialize(self, encoded):
        if len(encoded) != 32:
            raise Exception("Invalid input length for decompression")
        y = int.from_bytes(encoded, "little")
        sign = int(y) >> 255
        y = int(int(y) & ((1 << 255) - 1))

        x = GroupEd25519.recover_x(y, sign, self.p, self.d)
        if x is None:
            return None
        else:
            (u, v) = GroupEd25519.to_weierstrass(self.a, self.F(self.d), x, y)
            point = self.curve(u, v)
            if point == self.identity():
                raise Exception("Identity element not permitted")
            return point

    def serialize_scalar(self, scalar):
        return int.to_bytes(int(scalar) % int(self.group_order), 32, "little")

    def element_byte_length(self):
        return 32

    def scalar_byte_length(self):
        return 32

    def hash_to_scalar(self, msg, dst=""):
        # From RFC8032. Note that the DST is ignored.
        return int.from_bytes(hashlib.sha512(msg).digest(), "little") % self.order()

class GroupEd448(Group):
    # Compute corresponding x-coordinate, with low bit corresponding to
    # sign, or return None on failure
    # https://datatracker.ietf.org/doc/html/rfc8032#section-5.2.3
    def recover_x(y, sign, p, d):
        if y >= p:
            return None
        u = y^2 - 1
        v = (d * y^2) - 1
        x = (u / v) ^ ((p+1) / 4)
        if (v * x^2) != u:
            return None
        if (int(x) & int(1)) != sign:
            x = p - x
        return x

    def to_weierstrass(a, d, x, y):
        return ((5*a + a*y - 5*d*y - d)/(12 - 12*y), (a + a*y - d*y -d)/(4*x - 4*x*y))

    def to_twistededwards(a, d, u, v):
        y = (5*a - 12*u - d)/(-12*u - a + 5*d)
        x = (a + a*y - d*y -d)/(4*v - 4*v*y)
        return (x, y)

    def __init__(self):
        Group.__init__(self, "ed448")
        # Borrowed from: https://neuromancer.sk/std/other/Ed448#
        p = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffffffffffffffffffffffffffffffffffffffffffffffffffff
        K = GF(p)
        a = K(0x01)
        d = K(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffffffffffffffffffffffffffffffffffffffffffffffff6756)
        E = EllipticCurve(K, (K(-1/48) * (a^2 + 14*a*d + d^2),K(1/864) * (a + d) * (-a^2 + 34*a*d - d^2)))
        G = E(*GroupEd448.to_weierstrass(a, d, K(0x4f1970c66bed0ded221d15a622bf36da9e146570470f1767ea6de324a3d3a46412ae1af72ab66511433b80e18b00938e2626a82bc70cc05e), K(0x693f46716eb6bc248876203756c9c7624bea73736ca3984087789c1e05a0c2d73ad3ff1ce67c39c4fdbd132c4ed7c8ad9808795bf230fa14)))
        order = 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffff7cca23e9c44edb49aed63690216cc2728dc58f552378c292ab5844f3 * 0x04
        E.set_order(order)

        self.F = K
        self.curve = E
        self.p = p
        self.group_order = 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffff7cca23e9c44edb49aed63690216cc2728dc58f552378c292ab5844f3
        self.G = G
        self.a = a
        self.d = d

    def generator(self):
        return self.G

    def order(self):
        return self.group_order

    def identity(self):
        return self.curve(0)

    def serialize(self, element):
        if element == self.identity():
            raise Exception("Identity element not permitted")

        (x, y) = element.xy()
        (u, v) = GroupEd448.to_twistededwards(self.a, self.d, x, y)

        sign = int(int(u) % 2)
        return int.to_bytes(int(v) | (sign << 455), 57, "little")

    def deserialize(self, encoded):
        if len(encoded) != 57:
            raise Exception("Invalid input length for decompression")
        y = int.from_bytes(encoded, "little")
        sign = int(y) >> 455
        y = int(int(y) & ((1 << 455) - 1))

        x = GroupEd448.recover_x(y, sign, self.p, self.d)
        if x is None:
            return None
        else:
            (u, v) = GroupEd448.to_weierstrass(self.a, self.F(self.d), x, y)
            point = self.curve(u, v)
            if point == self.identity():
                raise Exception("Identity element not permitted")
            return point

    def serialize_scalar(self, scalar):
        return int.to_bytes(int(scalar) % int(self.group_order), 57, "little")

    def element_byte_length(self):
        return 57

    def scalar_byte_length(self):
        return 57

    def hash_to_scalar(self, msg, dst=""):
        # From RFC8032. Note that the DST is ignored.
        return int.from_bytes(hashlib.shake_256(msg).digest(int(114)), "little") % self.order()

class GroupRistretto255(Group):
    def __init__(self):
        Group.__init__(self, "ristretto255")
        self.k = 128
        self.L = 48
        self.field_bytes_length = 32

    def generator(self):
        return Ed25519Point().base()

    def order(self):
        return Ed25519Point().order

    def identity(self):
        return Ed25519Point().identity()

    def serialize(self, element):
        if element == self.identity():
            raise Exception("Identity element not permitted")

        return element.encode()

    def deserialize(self, encoded):
        element = Ed25519Point().decode(encoded)

        if element == self.identity():
            raise Exception("Identity element not permitted")

        return element

    def serialize_scalar(self, scalar):
        return I2OSP(scalar % self.order(), self.scalar_byte_length())[::-1]

    def element_byte_length(self):
        return self.field_bytes_length

    def scalar_byte_length(self):
        return self.field_bytes_length

    def hash_to_scalar(self, msg, dst=""):
        return hash_to_field(msg, 1, dst, self.order(), 1, self.L, expand_message_xmd, hashlib.sha512, self.k)[0][0]

