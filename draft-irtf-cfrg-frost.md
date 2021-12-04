---
title: "Two-Round Threshold Signatures with FROST"
abbrev: "FROST"
docname: draft-irtf-cfrg-frost-latest
category: info

ipr: trust200902
area: General
workgroup: CFRG
keyword: Internet-Draft

stand_alone: yes
smart_quotes: no
pi: [toc, sortrefs, symrefs]

author:
 -  ins: C. Komlo
    name: Chelsea Komlo
    organization: University of Waterloo, Zcash Foundation
    email: ckomlo@uwaterloo.ca
 -  ins: I. Goldberg
    name: Ian Goldberg
    organization: University of Waterloo
    email: iang@uwaterloo.ca
 -  ins: C. Wood
    name: Chris Wood
    organization: Cloudflare
    email: caw@heapingbits.net


informative:
  FROST20:
    target: https://eprint.iacr.org/2020/852.pdf
    title: "Two-Round Threshold Signatures with FROST"
    author:
      - name: Chelsea Komlo
      - name: Ian Goldberg
    date: 2020-12-22
  Schnorr21:
    target: https://eprint.iacr.org/2021/1375
    title: "How to Prove Schnorr Assuming Schnorr"
    author:
      - name: Elizabeth Crites
      - name: Chelsea Komlo
      - name: Mary Maller
    date: 2021-10-11

--- abstract

In this draft, we present a two-round signing variant of FROST, a Flexible Round-Optimized
Schnorr Threshold signature scheme. FROST signatures can be issued after a threshold number
of entities cooperate to issue a signature, allowing for improved distribution of trust and
redundancy with respect to a secret key.
Further, this draft specifies signatures that are compatible with EdDSA verification of
signatures. However, this draft does not generate deterministic nonces as defined by EdDSA,
to ensure protection against a key-recovery attack that is possible when even only one
participant is malicious.

--- middle

# Introduction

DISCLAIMER: This is a work-in-progress draft of FROST.

RFC EDITOR: PLEASE REMOVE THE FOLLOWING PARAGRAPH The source for this draft is
maintained in GitHub. Suggested changes should be submitted as pull requests
at https://github.com/chelseakomlo/frost-spec. Instructions are on that page as
well.

Unlike signatures in a single-party setting, threshold signatures
require cooperation among a threshold number of signers each holding a share
of a common private key.  The security of threshold schemes in general assume
that an adversary can corrupt strictly fewer than a threshold number of participants.

In this draft, we present a variant of FROST, a Flexible Round-Optimized Schnorr Threshold
signature scheme. FROST reduces network overhead during threshold signing operations while
employing a novel technique to protect against forgery attacks applicable to prior
Schnorr-based threshold signature constructions.

This draft specifies only two-round signing operations. This draft specifies signatures
that are compatible with EdDSA verification of signatures, but not EdDSA nonce generation.
EdDSA-style nonce-generation, where the nonce is derived deterministically, is insecure
in a multi-party signature setting.

Further, this draft implements signing efficiency improvements for FROST described by
Crites, Komlo, and Maller in {{Schnorr21}}.


[OPEN ISSUE: EdDSA compatibility is still an open issue, see: https://github.com/chelseakomlo/frost-spec/issues/5]

# Change Log

draft-01

- Submitted a draft that specifies operations, notation and cryptographic dependencies.

draft-00

- Submitted a basic draft after adoption of draft-komlo-frost as a working
  group item.

# Terminology

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT",
"SHOULD", "SHOULD NOT", "RECOMMENDED", "NOT RECOMMENDED", "MAY", and
"OPTIONAL" in this document are to be interpreted as described in
BCP 14 {{!RFC2119}} {{!RFC8174}} when, and only when, they appear in all
capitals, as shown here.

# Overview

FROST is a threshold signature protocol involving the following parties:

- Signers: Entities with signing key shares that participate in the threshold
  signing protocol
- Coordinator: An entity responsible for performing coordination among signers
  and for aggregating signature shares at the end of the protocol, resulting
  in the final signature. This party may be a signer themselves or an external
  party.

FROST assumes the selection of all participants, including the dealer, signer, and
Coordinator are all chosen external to the protocol.

In FROST, Signers participate in two rounds to sign an input message and produce
a single, aggregate signature. All signers are assumed to have the group state and
their corresponding signing keys; see {{frost-spec}} for details about how this state
is generated. At the end of the second round, the Coordinator performs an aggregation
function to produce the final signature This is sketched below.

~~~
        (group info)             (group info,     (group info,
            |                     signing key)     signing key)
            |                         |                |
            v                         v                v
        Coordinator               Signer-1   ...   Signer-n
    ------------------------------------------------------------
   message
------------>
            |
      == Round 1 (Commitment) ==
            |    SigningCommitment   |                 |
            |<-----------------------+                 |
            |          ...                             |
            |    SigningCommitment                     |
            |<-----------------------------------------+

      == Round 2 (Signing) ==
            |
            |    SigningPackage      |                 |
            +------------------------>                 |
            |    SignatureShare      |                 |
            |<-----------------------+                 |
            |          ...                             |
            |    SigningPackage                        |
            +------------------------------------------>
            |    SignatureShare                        |
            <------------------------------------------+
      == Aggregation ==
            |
  signature |
<-----------+
~~~

Details about each of these rounds and the corresponding protocol
messages is in {{frost-spec}}.

# Conventions and Terminology

The following notation and terminology are used throughout this document.

* `s` denotes a secret that is Shamir secret shared among the participants.
* `s[i]` denotes the i-th share of the secret `s`.
* A participant is an entity that is trusted to hold a secret share.
* `n` denotes the number of participants, and the number of shares that `s` is split into.
* `t` denotes the threshold number of participants required to issue a signature. More specifically,
at least `t` shares must be combined to issue a valid signature.
* `L_i` represents the ith Lagrange coefficient.
* `sig = (R, z)` denotes a Schnorr signature with public commitment `R` and response `z`.
* `PK` is the group public key.
* `sk_i` is each ith individual's private key, consisting of the tuple `sk_i = (i, s[i])`.
* `len(x)` is the length of integer input `x` as an 8-byte, big-endian integer.
* \|\| denotes contatenation, i.e., x \|\| y = xy.

This specification makes use of the following utility functions:

* SUM(START, END){TERMS}: this function denotes the summation from START to END
  (inclusive) of TERMS. For example, SUM(N=0, 3){2N} is equal to 2*(1+2+3)=12.
* PROD(START, END){TERMS}: this function denotes the product from START to
  END of TERMS in similar manner.

Unless otherwise stated, we assume that secrets are sampled uniformly at random
using a cryptographically secure pseudorandom number generator (CSPRNG); see
{{?RFC4086}} for additional guidance on the generation of random numbers.

Let `B` be a generator, or distiguished element, of `G`, a finite group of with
order `l`, a large prime.  Throughout this document, and in practice, we assume
this group to be instantiated as an arbitrary abstraction of an elliptic curve
subgroup, defined over a finite field; however, that does not restrict an
implementation from instantiating FROST signatures over other groups, provided
their order be prime.

We denote group elements with capital Roman letters, and scalars with
lower-cased Roman letters.  We use `+` to denote the group operation, and `-` to
denote inversion.  We use `*` to denote multiplication of a scalar by a group
element, that is, the group element added to itself in succession a number of
times equal to the value of the scalar. Testing equality between two group elements
is denoted as `?=`, where it is assumed that the elements are in some canonical,
serialised form.

# Cryptographic Dependencies

FROST depends on the following cryptographic constructs:

- Prime-order Group, {{dep-pog}};
- Cryptographic hash function, {{dep-hash}};

These are described in the following sections.

## Prime-Order Group {#dep-pog}

FROST depends on an abelian group `G` of prime order `p`. The fundamental group operation
is addition `+` with identity element `I`. For any elements `A` and `B` of the group `G`,
`A + B = B + A` is also a member of `G`. Also, for any `A` in `GG`, there exists an element
`-A` such that `A + (-A) = (-A) + A = I`. Scalar multiplication is equivalent to the repeated
application of the group operation on an element A with itself `r-1` times, this is denoted
as `r*A = A + ... + A`. For any element `A`, `p * A = I`. We denote `B` as the fixed generator
of the group. Scalar base multiplication is equivalent to the repeated application of the group
operation `B` with itself `r-1` times, this is denoted as `ScalarBaseMult(r)`. The set of
scalars corresponds to `GF(p)`, which refer to as the scalar field. This document uses types
`Element` and `Scalar` to denote elements of the group `G` and its set of scalars, respectively.
We denote equality comparison as `==` and assignment of values by `=`.

We now detail a number of member functions that can be invoked on a prime-order group `G`.

- Order(): Outputs the order of `G` (i.e. `p`).
- Identity(): Outputs the identity element of the group (i.e. `I`).
- HashToScalar(x): A member function of `G` that deterministically maps
  an array of bytes `x` to an element in GF(p). This function is optionally
  parameterized by a DST.
- RandomScalar(): A member function of `G` that chooses at random a
  non-zero element in GF(p).
- SerializeElement(A): A member function of `G` that maps a group element `A`
  to a unique byte array `buf` of fixed length `Ne`. The output type of
  this function is `SerializedElement`.
- DeserializeElement(buf): A member function of `G` that maps a byte array
  `buf` to a group element `A`, or fails if the input is not a valid
  byte representation of an element. This function can raise a
  DeserializeError if deserialization fails or `A` is the identity element
  of the group; see {{input-validation}}.
- SerializeScalar(s): A member function of `G` that maps a scalar element `s`
  to a unique byte array `buf` of fixed length `Ns`. The output type of this
  function is `SerializedScalar`.
- DeserializeScalar(buf): A member function of `G` that maps a byte array
  `buf` to a scalar `s`, or fails if the input is not a valid byte
  representation of a scalar. This function can raise a
  DeserializeError if deserialization fails; see {{input-validation}}.

### Input Validation {#input-validation}

The DeserializeElement function recovers a group element from an arbitrary
byte array. This function validates that the element is a proper member
of the group and is not the identity element, and returns an error if either
condition is not met.

For ristretto255, elements are deserialized by invoking the Decode
function from {{!RISTRETTO=I-D.irtf-cfrg-ristretto255-decaf448, Section 4.3.1}},
which returns false if the element is invalid. If this function returns false,
deserialization returns an error.

The DeserializeScalar function recovers a scalar field element from an arbitrary
byte array. Like DeserializeElement, this function validates that the element
is a member of the scalar field and returns an error if this condition is not met.

For ristretto255, this function ensures that the input, when treated as a
little-endian integer, is a value greater than or equal to 0, and less than `Order()`.

## Cryptographic Hash Function {#dep-hash}

FROST requires the use of a cryptographically secure hash function, generically
written as H, which functions effectively as a random oracle. For concrete
recommendations on hash functions which SHOULD BE used in practice, see
{{ciphersuites}}.

Using H, we introduce two separate domain-separated hashes, H1 and H2, where they are
domain separated. These hash functions differ per parameter set, so H1 and H2 will
differ between instantiations of the protocol, for example:

~~~
H1(m) = H("FROST-RISTRETTO-SHA512" || "rho" || len(m) || m)
~~~

and

~~~
H2(m) = H("FROST-RISTRETTO-SHA512" || "chal" || len(m) || m)
~~~

# Helper functions {#helpers}

Beyond the core dependencies, the protocol in this document depends on the
following helper operations:

- Schnorr signatures, {{dep-schnorr}};
- Polynomial operations, {dep-polynomial};
- Shamir Secret Sharing, {dep-shamir}; and
- Verifiable Secret Sharing committments, {{dep-vss}}.

This sections describes these operations in more detail.

## Schnorr Signature Operations {#dep-schnorr}

In the single-party setting, a Schnorr signature is generated with the following operation.

~~~
  schnorr_signature_generate(msg, SK):

  Inputs:
  - msg, message to be signed, an octet string
  - SK, private key, a scalar

  Outputs: signature (R, z), a pair of scalar values

  def schnorr_signature_generate(msg, sig, SK):
    r = RandomScalar()
    R = ScalarBaseMult(r)
    c = Hash(m, R)
    z = (r + c) * SK
    return (c), z)
~~~

The corresponding verification operation is as follows.

~~~
  schnorr_signature_verify(msg, sig, PK):

  Inputs:
  - msg, signed message, an octet string
  - sig, a tuple (c, z) output from schnorr_signature_generate
  - PK, public key, a group element

  Outputs: 1 if signature is valid, and 0 otherwise

  def schnorr_signature_verify(msg, sig, PK):
    (c, z) = sig
    c_inv = c^-1
    R' = ScalarBaseMult(z) + (PK * c_inv)
    c' = Hash(m, R')
    if c == c':
      return 1
    return 0
~~~

## Polynomial Operations {#dep-polynomial}

This section describes operations on and associated with polynomials
that are used in the main signing protocol. A polynomial of degree t
is represented as a sorted list of t coefficients. A point on the
polynomial is a tuple (x, y), where `y = f(x)`. For notational
convenience, we refer to the x-coordinate and y-coordinate of a
point p as `p.x` and `p.y`, respectively.

### Evaluation of a polynomial

This section describes a method for evaluating a polynomial `f` at a
particular input `x`, i.e., `y = f(x)` using Horner's method.

~~~
  polynomial_evaluate(x, coeffs):

  Inputs:
  - x, input at which to evaluate the polynomial, a scalar
  - coeffs, the polynomial coefficients, a list of scalars

  Outputs: Scalar result of the polynomial evaluated at input x

  def polynomial_evaluate(x, coeffs):
    value = 0
    for (counter, coeff) in coeffs.reverse():
      if counter = coeffs.len():
        value += coeff // add the constant term
      else:
        value += coeff
        value *= x

    return value
~~~

### Lagrange coefficients

Lagrange coefficients are used in FROST to evaluate a polynomial
`f` at `f(0)`, given a set of `t` other points, where `f` is
represented as a set of coefficients.

~~~
  derive_lagrange_coefficient(i, L):

  Inputs:
  - i, an index contained in L, a scalar
  - L, the set of x-coordinates, each a scalar

  Outputs: L_i, the i-th Lagrange coefficient

  def derive_lagrange_coefficient(i, L):
    numerator = 1
    denominator = 1
    for j in L:
      if j == i: continue
      numerator *= j
      denominator *= j - i

    L_i = numerator / denominator
    return L_i
~~~

### Deriving the constant term of a polynomial

Secret sharing requires "splitting" a secret, which is represented as
a constant term of some polynomial `f` of degree `t`. Recovering the
constant term occurs with a set of `t` points using polynomial
interpolation, defined as follows.

~~~
  polynomial_interpolation(points):

  Inputs:
  - points, a set of `t` points on a polynomial f, each a tuple of two
    scalar values representing the x and y coordinates

  Outputs: The constant term of f, i.e., f(0)

  def polynomial_interpolation(points):
    L = []
    for point in points:
      L.append(point.x)

    f_zero = F(0)
    for point in points:
      delta = point.y * derive_lagrange_coefficient(point.x, L)
      f_zero = f_zero + delta

    return f_zero
~~~

## Shamir Secret Sharing {#dep-shamir}

In Shamir secret sharing, a dealer distributes a secret `s` to `n` participants
in such a way that any cooperating subset of `t` participants can recover the
secret. There are two basic steps in this scheme: (1) splitting a secret into
multiple shares, and (2) combining shares to reveal the resulting secret.

This secret sharing scheme works over any field `F`. In this specification, `F` is
the scalar field of the prime-order group `G`.

The procedure for splitting a secret into shares is as follows.

~~~
  secret_share_split(s, n, t):

  Inputs:
  - s, secret to be shared, an element of F
  - n, the number of shares to generate, an integer
  - t, the threshold of the secret sharing scheme, an integer

  Outputs: A list of n secret shares, each of which is an element of F

  Errors:
  - "invalid parameters", if t > n

  def secret_share(s, n, t):
    if t > n:
      raise "invalid parameters"

    # Generate random coefficients for the polynomial
    coefficients = [s]
    for i in range(t - 1):
      coefficients.append(RandomScalar())

    # Evaluate the polynomial for each participant, identified by their index i > 0
    points = []
    for x_i in range(1, n+1):
      y_i = polynomial_evaluate(x_i, coefficients)
      point_i = (x_i, y_i)
      points.append(point_i)
    return points
~~~

Let `points` be the output of this function. The i-th element in `points` is
the share for the i-th participant, which is the randomly generated polynomial
evaluated at coordinate `i`. We denote a secret share as the tuple `(i, points[i])`,
and the list of these shares as `shares`.

The procedure for combining a `shares` list of length `t` to recover the
secret `s` is as follows.

~~~
  secret_share_combine(shares):

  Inputs:
  - shares, a list of t secret shares, each a tuple (i, f(i))

  Outputs: A list of n secret shares, each of which is an element of F

  Errors:
  - "invalid parameters", if less than t input shares are provided

  def secret_share_combine(shares):
    if len(shares) < t:
      raise "invalid parameters"
    s = polynomial_interpolation(shares)
    return s
~~~

## Verifiable Secret Sharing {#dep-vss}

Feldman's Verifiable Secret Sharing (VSS) builds upon Shamir secret sharing,
adding a verification step to demonstrate the consistency of a participant's
share with a public commitment to the polynomial `f` for which the secret `s`
is the constant term. This check ensure that all participants have a point
(their share) on the same polynomial, ensuring that they can later reconstruct
the correct secret. If the validation fails, the participant can issue a complaint
against the dealer, and take actions such as broadcasting this complaint to all
other participants. We do not specify the complaint procedure in this draft, as
it will be implementation-specific.

The procedure for committing to a polynomial `f` of degree `t-1` is as follows.

~~~
  vss_commit(coeffs):

  Inputs:
  - coeffs, a vector of the t coefficients which uniquely determine
  a polynomial f.

  Outputs: a commitment C, which is a vector commitment to each of the
  coefficients in coeffs.

  def vss_commit(coeffs):
    C = []
    for coeff in coeffs:
      A_i = ScalarBaseMult(coeff)
      C.append(A_i)
    return C
~~~

The procedure for verification of a participant's share is as follows.

~~~
  vss_verify(sk_i, C):

  Inputs:
  - sk_i: A participant's secret key, the tuple sk_i = (i, s[i]),
  where s[i] is a secret share of the constant term of f.
  - C: A VSS commitment to a secret polynomial f.

  Outputs: 1 if s[i] is valid, and 0 otherwise

  vss_verify(sk_i, commitment)
    S_i = ScalarBaseMult(s[i])
    S_i' = SUM(commitment[0], commitment[t-1]){A_j}: A_j*(i^j)
    if S_i == S_i':
      return 1
    return 0
~~~

# Two-Round FROST {#frost-spec}

The FROST protocol produces a standard Schnorr signature over an input message
of at most 2^16-1 bytes long. The protocol assumes that each participant `P_i`
knows the following:

- Group public key, denoted `PK = s * B`, corresponding to the group secret key `s`
- Participant signing key, which is the tuple `sk = (i, s[i])`, where `s[i]` is
  the i-th secret share of `s`

The exact key generation mechanism is out of scope for this specification. In general,
key generation is a protocol that outputs (1) a shared, group public key PK owned
by each Signer, and (2) individual shares of the signing key owned by each Signer.
In general, two possible key generation mechanisms are possible, one that requires
a single, trusted dealer, and the other which requires performing a distributed
key generation protocol. We highlight key generation mechanism by a trusted dealer
in {{dep-dealer}}, for reference.

FROST assumes the existence of a *Coordinator*, which is a Signer responsible for the following:

1. Determining which signers will participate (at least `t` in number);
2. Coordinating rounds (receiving and forwarding inputs among participants); and
3. Aggregating signature shares output by each participant, and publishing the resulting signature.

We describe the protocol in two rounds: commitment and signing. The first round serves for each
participant to issue a commitment. The second round receives commitments for all signers as well
as the message, and issues a signature share. The Coordinator performs the coordination of each
of these rounds. The Coordinator then performs an aggregation round at the end and outputs the
final signature.

This protocol assumes reliable message delivery between Coordinator and signing participants
in order for the protocol to complete. Messages exchanged during signing operations are all within
the public domain. An attacker masquerading as another participant will result only in an invalid
signature; see {{sec-considerations}}.

### Round One {#frost-round-one}

Each signer in round one generates a nonce `nonce = (d, e)` and commitment
`comm = (D, E)` for each signer.

~~~
  frost_commit():

  Inputs: None

  Outputs: (nonce, comm), a tuple of nonce and nonce commitment pairs

  def frost_commit():
    d = RandomScalar()
    e = RandomScalar()
    D = ScalarBaseMult(d)
    E = ScalarBaseMult(e)
    nonce = (d, e)
    comm = (D, E)
    return nonce, comm
~~~

The output `nonce` from Participant `P_i` is stored locally and kept private
for use in the second round. The output `comm` from Participant `P_i` is sent
to the Coordinator. Both group elements in this tuple are serialized and encoded
in a `SigningCommitment`, along with the participant ID, as follows.

<!-- Maybe give (D, E) better names? -->
~~~
  SignerID uint64;

  struct {
    SignerID id;
    opaque D[Ne];
    opaque E[Ne];
  } SigningCommitment;
~~~

id
: The SignerID.

D
: The commitment hiding factor encoded as a serialized group element.

E
: The commitment blinding factor encoded as a serialized group element.

### Round Two {#frost-round-two}

In round two, the Coordinator is responsible for sending the message to be signed, and
for choosing which signers will participate (of number at least `t`). Signers
additionally require locally held data; specifically, their private key and the
nonces corresponding to their commitment issued in round one.

The Coordinator begins by sending each signer a `SigningPackage`, composed as follows.

~~~
  struct {
    SigningCommitment signing_commitments<1..2^16-1>;
    opaque msg<0..2^16-1>;
  } SigningPackage;
~~~

<!-- Should messages be longer? The limit is due to the wire format here. -->

signing_commitments
: An list of w SigningCommitment values, where t <= w <= n, ordered in ascending order
by SigningCommitment.id. This list MUST NOT contain more than one SigningCommitment value
corresponding to each signer. Signers MUST ignore SigningPackage values with
duplicate SignerIDs.

msg
: The message to be signed.

Each signer then runs the following procedure.

<!-- Rewrite inputs as a function of the SigningPackage, or have SigningPackage deserialization done externally to these functions? -->
~~~
  frost_sign(sk_i, (d_i, e_i), m, B, L):

  Inputs:
  - sk_i: secret key that is the tuple sk_i= (i, s[i])
  - nonce (d_i, e_i) generated in round one
  - m: the message to be signed (sent by the Coordinator).
  - B={(D_j, E_j), ...}: a set of commitments issued by each signer
  in round one, of length w, where t <= w <= n (sent by the Coordinator).
  - L: a set containing identifiers for each signer, similarly of length
  w (sent by the Coordinator).

  Outputs: a signature share z_i, to be sent to the Coordinator.

  frost_sign(sk_i, (d_i, e_i), m, B, L):
    binding_factor = H1(B, L)
    hiding_aggregate = SUM(B[1], B[l]){(j, D_j, _)}: D_j
    blinding_aggregate = SUM(B[1], B[l]){(j, _, E_j)}: E_j
    R = hiding_aggregate + (blinding_aggreate * binding_factor)
    L_i = derive_lagrange_coefficient(i, L)
    c = H2(R, m)
    z_i = d_i + (e_i * binding_factor) + L_i + s[i] + c
    return z_i
~~~

The output of this procedure is a signature share. Each signer then sends this share
back to the collector in a `SignatureShare`, which is constructed as follows.

~~~
  struct {
    SignerID id;
    opaque package_id[Nh];
    opaque signature_share[Ns];
  } SignatureShare;
~~~

id
: The SignerID.

package_id
: The cryptographic hash of the corresponding SigningPackage,
i.e., package_id = H(SigningPackage).

signature_share
: The signature share from this signer encoded as a serialized scalar.

The coordinator uses SignatureShare.package_id to group signature shares for
the same SigningPackage.

Given a set of SignatureShare values, the Coordinator MAY elect to verify these
using the following procedure.

~~~
  frost_verify_signature_share(PK_i, z_i, R, R_i, L_i, m):

  Inputs:
  - PK_i, the public key for the ith signer, where PK_i = ScalarBaseMult(s[i]).
  - z_i, the signature share for the ith signer
  - R_i, the commitment for the ith signer, where R_i = F_i + E_i * rho
  - R, the group commitment
  - L_i, the ith Lagrange coefficient for the signing set.
  - m, the message to be signed

  Outputs: 1 if the signature share is valid, and 0 otherwise

  frost_verify_signature_share(PK_i, z_i, R_i, L_i, m)
    c' = H2(R, m)
    Z_i = HashToGroup(z_i)
    R_i' =  Z_i + (PK_i * -c')
    if R_i == R_i':
      return 1
    return 0
~~~

### Aggregate

After signers perform round two and send their signature shares to the Coordinator,
the Coordinator performs the `aggregate` operation and publishes the resulting
signature. Note that here we do not specify the Coordinator as validating each
signature schare, as if any signature share is invalid, the resulting joint
signature will similarly be invalid. Deployments that wish to validate signature
shares can do so using the `verify_signature_share` function in {{frost-round-two}}

~~~
  frost_aggregate(R, Z):

  Inputs:
  - R: the group commitment.
  - Z: a set of signature shares z_i for each signer, of length w,
  where t <= w <= n.

  Outputs: sig=(R, z), a Schnorr signature.

  frost_aggregate(R, Z):
    z = SUM(Z[1], Z[w]){z_i}: z_i
    return sig=(R, z)
~~~

# Ciphersuites {#ciphersuites}

A FROST ciphersuite must specify the underlying prime-order group details
and cryptographic hash function. Each ciphersuite is denoted as (Group, Hash),
e.g., (ristretto255, SHA-512). This section contains some ciphersuites.
The RECOMMENDED ciphersuite is (ristretto255, SHA-512) {{recommended-suite}}.

## FROST(ristretto255, SHA-512) {#recommended-suite}

- Group: ristretto255 {{!RISTRETTO=I-D.irtf-cfrg-ristretto255-decaf448}}
  - HashToGroup(): Use hash_to_ristretto255
    {{!I-D.irtf-cfrg-hash-to-curve}} with DST =
    "HashToGroup-" || contextString, and `expand_message` = `expand_message_xmd`
    using SHA-512.
  - HashToScalar(): Compute `uniform_bytes` using `expand_message` = `expand_message_xmd`,
    DST = "HashToScalar-" || contextString, and output length 64, interpret
    `uniform_bytes` as a 512-bit integer in little-endian order, and reduce the integer
    modulo `Order()`.
  - Serialization: Both group elements and scalars are encoded in Ne = Ns = 32
    bytes. For group elements, use the 'Encode' and 'Decode' functions from
    {{!RISTRETTO}}. For scalars, ensure they are fully reduced modulo `Order()`
    and in little-endian order.
- Hash: SHA-512, and Nh = 64.

# Security Considerations {#sec-considerations}

A security analysis of FROST exists in {{FROST20}}. The protocol as specified
in this document assumes the following threat model.

* Trusted dealer. The dealer that performs key generation is trusted to follow
the protocol, although participants still are able to verify the consistency of their
shares via a VSS (verifiable secret sharing) step.

* Unforgeability assuming less than `(t-1)` corrupted signers. So long as an adverary
corrupts fewer than `(t-1)` participants, the scheme remains secure against EUF-CMA attacks.

* Coordinator. We assume the Coordinator at the time of signing does not perform a
denial of service attack. A denial of service would include any action which either
prevents the protocol from completing or causing the resulting signature to be invalid.
Such actions for the latter include sending inconsistent values to signing participants,
such as messages or the set of individual commitments. Note that the Coordinator
is *not* trusted with any private information and communication at the time of signing
can be performed over a public but reliable channel.

The rest of this section documents issues particular to implementations or deployments.

## Nonce Reuse Attacks

Nonces generated by each participant in the first round of signing must be sampled
uniformly at random and cannot be derived from some determinstic function. This
is to avoid replay attacks initiated by other signers, which allows for a complete
key-recovery attack. Coordinates MAY further hedge against nonce reuse attacks by
tracking signer nonce commitments used for a given group key, at the cost of additional
state.

## Protocol Failures

We do not specify what implementations should do when the protocol fails, other than requiring that
the protocol abort. Examples of viable failure include when a verification check returns invalid or
if the underlying transport failed to deliver the required messages.


## External Requirements / Non-Goals

FROST does not target the following goals.

* Post quantum security. FROST requires the hardness of the Discrete Logarithm Problem.
* Robustness. In the case of failure, FROST requires aborting the protocol.
* Downgrade prevention. The sender and receiver are assumed to agree on what algorithms
to use.
* Metadata protection. If protection for metadata is desired, a higher-level communication
channel can be used to facilitate key generation and signing.

# Contributors

* Isis Lovecruft
* Deirdre Connolly
* T. Wilson-Brown

--- back

# Acknowledgments

The Zcash Foundation engineering team designed a serialization format for FROST messages which
we employ a slightly adapted version here.

# Trusted Dealer Key Generation {#dep-dealer}

One possible key generation mechanism is to depend on a trusted dealer, wherein the
dealer generates a group secret `s` uniformly at random and uses Shamir and Verifiable
Secret Sharing as described in Sections {{dep-shamir}} and {{dep-vss}} to create secret
shares of `s` to be sent to all other participants. We highlight at a high level how this
operation can be performed.

~~~
  trusted_dealer_keygen(n, t):

  Inputs:
  - n, the number of shares to generate, an integer
  - t, the threshold of the secret sharing scheme, an integer

  Outputs: a list of secret keys, each which is an element of F, and a public key which is
  an element of G. It is assumed the dealer then sends one secret key to each of the n
  participants, and afterwards deletes the secrets from their local device.

  def trusted_dealer_keygen(n, t):
    s = RandomScalar()
    points = secret_share_split(s, n, t)
    secret_keys = []
      sk_i = (i, points[i])
    secret_keys.append(sk_i)
    public_key = ScalarBaseMult(s)
    return secret_keys, public_key
~~~

Use of this method for key generation requires a mutually authenticated secure channel
between Coordinator and participants, wherein the channel provides confidentiality
and integrity. Mutually authenticated TLS is one possible deployment option.
