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
 -  ins: D. Connolly
    name: Deirdre Connolly
    organization: Zcash Foundation
    email: durumcrustulum@gmail.com
 -  ins: C. Komlo
    name: Chelsea Komlo
    organization: University of Waterloo, Zcash Foundation
    email: ckomlo@uwaterloo.ca
 -  ins: I. Goldberg
    name: Ian Goldberg
    organization: University of Waterloo
    email: iang@uwaterloo.ca
 -  ins: C. A. Wood
    name: Christopher A. Wood
    organization: Cloudflare
    email: caw@heapingbits.net

normative:
  x9.62:
    title: "Public Key Cryptography for the Financial Services Industry: the Elliptic Curve Digital Signature Algorithm (ECDSA)"
    date: Sep, 1998
    seriesinfo:
      "ANSI": X9.62-1998
    author:
      -
        org: ANSI
  SECG:
    title: "Elliptic Curve Cryptography, Standards for Efficient Cryptography Group, ver. 2"
    target: https://secg.org/sec1-v2.pdf
    date: 2009
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

<!-- I don't think this EdDSA compatibility claim holds right now, we need to check! -->

--- middle

# Introduction

DISCLAIMER: This is a work-in-progress draft of FROST.

RFC EDITOR: PLEASE REMOVE THE FOLLOWING PARAGRAPH The source for this draft is
maintained in GitHub. Suggested changes should be submitted as pull requests
at https://github.com/cfrg/draft-irtf-cfrg-frost. Instructions are on that page as
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
            |
      == Aggregation ==
            |
  signature |
<-----------+
~~~

Details about each of these rounds and the corresponding protocol
messages is in {{frost-spec}}.

# Conventions and Terminology

The following notation and terminology are used throughout this document.

* A participant is an entity that is trusted to hold a secret share.
* `NUM_SIGNERS` denotes the number of participants, and the number of shares that `s` is split into.
  This value MUST NOT exceed 2^16-1.
* `THRESHOLD_LIMIT` denotes the threshold number of participants required to issue a signature. More specifically,
at least THRESHOLD_LIMIT shares must be combined to issue a valid signature.
* `len(x)` is the length of integer input `x` as an 8-byte, big-endian integer.
* `I2OSP(x, w)`: Convert non-negative integer `x` to a `w`-length,
  big-endian byte string as described in {{!RFC8017}}.
* `OS2IP(s)`: Convert byte string `s` to a non-negative integer as
  described in {{!RFC8017}}, assuming big-endian byte order.
* \|\| denotes contatenation, i.e., x \|\| y = xy.

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
{{ciphersuites}}. Using H, we introduce three separate domain-separated hashes,
H1, H2, and H3, where H1 and H2 map arbitrary inputs to non-zero Scalar elements of
the prime-order group scalar field, and H3 is an alias for H with domain separation
applied. The details of H1, H2, and H3 vary based on ciphersuite. See {{ciphersuites}}
for more details about each.

# Helper functions {#helpers}

Beyond the core dependencies, the protocol in this document depends on the
following helper operations:

- Schnorr signatures, {{dep-schnorr}};
- Polynomial operations, {{dep-polynomial}};
- Encoding operations, {{dep-encoding}}

This sections describes these operations in more detail.

## Schnorr Signature Operations {#dep-schnorr}

In the single-party setting, a Schnorr signature is generated with the
following operation.

~~~
  schnorr_signature_generate(msg, SK):

  Inputs:
  - msg, message to be signed, an octet string
  - SK, private key, a scalar
  - PK, public key, a group element

  Outputs: signature (R, z), a pair of scalar values

  def schnorr_signature_generate(msg, SK, PK):
    r = G.RandomScalar()
    R = G.ScalarBaseMult(r)

    msg_hash = H3(msg)
    comm_enc = G.SerializeElement(R)
    pk_enc = G.SerializeElement(PK)
    challenge_input = group_comm_enc || group_public_key_enc || msg_hash
    c = H2(challenge_input)

    z = r + (c * SK)
    return (R, z)
~~~

The corresponding verification operation is as follows.

~~~
  schnorr_signature_verify(msg, sig, PK):

  Inputs:
  - msg, signed message, an octet string
  - sig, a tuple (R, z) output from schnorr_signature_generate or FROST
  - PK, public key, a group element

  Outputs: 1 if signature is valid, and 0 otherwise

  def schnorr_signature_verify(msg, sig = (R, z), PK):
    msg_hash = H3(msg)
    comm_enc = G.SerializeElement(R)
    pk_enc = G.SerializeElement(PK)
    challenge_input = group_comm_enc || group_public_key_enc || msg_hash
    c = H2(challenge_input)

    l = ScalarBaseMult(z)
    r = R + (c * PK)
    if l == r:
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
      if counter == coeffs.len() - 1:
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

## Encoding Operations {#dep-encoding}

This section describes various helper functions used for encoding data
structures into values that can be processed with hash functions.

~~~
  Inputs:
  - commitment_list = [(i, x_i, y_i), ...], a list of commitments issued by each signer,
    where each element in the list indicates the signer index i and their
    two commitment Element values (x_i, y_i). This list MUST be sorted in ascending order
    by signer index.

  Outputs: A byte string containing the serialized representation of commitment_list.

  def encode_group_commitment_list(commitment_list):
    encoded_group_commitment = nil
    for (index, hiding_nonce_commitment, binding_nonce_commitment) in commitment_list:
      encoded_commitment = I2OSP(index, 2) ||
                           G.SerializeElement(hiding_nonce_commitment) ||
                           G.SerializeElement(binding_nonce_commitment)
      encoded_group_commitment = encoded_group_commitment || encoded_commitment
    return encoded_group_commitment
~~~

# Two-Round FROST {#frost-spec}

The FROST protocol produces a standard Schnorr signature over an input message
of at most 2^16-1 bytes long. The protocol assumes that each participant `P_i`
knows the following:

- Group public key, denoted `PK = G.ScalarMultBase(s)`, corresponding to the group secret key `s`.
- Participant i signing key, which is the i-th secret share of `s`.

The exact key generation mechanism is out of scope for this specification. In general,
key generation is a protocol that outputs (1) a shared, group public key PK owned
by each Signer, and (2) individual shares of the signing key owned by each Signer.
In general, two possible key generation mechanisms are possible, one that requires
a single, trusted dealer, and the other which requires performing a distributed
key generation protocol. We highlight key generation mechanism by a trusted dealer
in {{dep-dealer}}, for reference.

FROST assumes the existence of a *Coordinator*, which is a Signer responsible for the following:

1. Determining which signers will participate (at least THRESHOLD_LIMIT in number);
2. Coordinating rounds (receiving and forwarding inputs among participants); and
3. Aggregating signature shares output by each participant, and publishing the resulting signature.

Selection of the Coordinator is outside the scope of this specification.

We describe the protocol in two rounds: commitment and signing. The first round serves for each
participant to issue a commitment. The second round receives commitments for all signers as well
as the message, and issues a signature share. The Coordinator performs the coordination of each
of these rounds. The Coordinator then performs an aggregation round at the end and outputs the
final signature.

This protocol assumes reliable message delivery between Coordinator and signing participants
in order for the protocol to complete. Messages exchanged during signing operations are all within
the public domain. An attacker masquerading as another participant will result only in an invalid
signature; see {{sec-considerations}}.

## Round One - Commitment {#frost-round-one}

<!-- Should we only require that the set of participants be selected and used in round 2? -->

Round one involves each signer generating a pair of nonces and their corresponding public
commitments. A nonce is a pair of Scalar values, and a commitment is a pair of Element values.

Each signer in round one generates a nonce `nonce = (hiding_nonce, binding_nonce)` and commitment
`comm = (hiding_nonce_commitment, binding_nonce_commitment)`.

~~~
  Inputs: None

  Outputs: (nonce, comm), a tuple of nonce and nonce commitment pairs.

  def commit():
    hiding_nonce = G.RandomScalar()
    binding_nonce = G.RandomScalar()
    hiding_nonce_commitment = G.ScalarBaseMult(hiding_nonce)
    binding_nonce_commitment = G.ScalarBaseMult(binding_nonce)
    nonce = (hiding_nonce, binding_nonce)
    comm = (hiding_nonce_commitment, binding_nonce_commitment)
    return (nonce, comm)
~~~

The private output `nonce` from Participant `P_i` is stored locally and kept private
for use in the second round. The public output `comm` from Participant `P_i`
is sent to the Coordinator; see {{encode-commitment}} for encoding recommendations.

<!-- The Coordinator must not get confused about which commitments come from which signers, do we need to say more about how this is done? -->

## Round Two - Signature Share Generation {#frost-round-two}

In round two, the Coordinator is responsible for sending the message to be signed, and
for choosing which signers will participate (of number at least THRESHOLD_LIMIT). Signers
additionally require locally held data; specifically, their private key and the
nonces corresponding to their commitment issued in round one.

The Coordinator begins by sending each signer the message to be signed along with the
set of signing commitments for other signers in the participant list. Upon receipt,
each Signer then runs the following procedure to produce its own signature share.

<!-- Rewrite inputs as a function of the SigningPackage, or have SigningPackage deserialization done externally to these functions? -->
~~~
  Inputs:
  - index, Index `i` of the signer. Note index will never equal `0`.
  - sk_i, Signer secret key share.
  - group_public_key, public key corresponding to the signer secret key share.
  - nonce_i, pair of Scalar values (d, e) generated in round one.
  - comm_i, pair of Element values (D, E) generated in round one.
  - msg, the message to be signed (sent by the Coordinator).
  - commitment_list = [(j, x_j, y_j), ...], a list of commitments issued by each signer,
    where each element in the list indicates the signer index j and their
    two commitment Element values (x_j, y_j). This list MUST be sorted in ascending order
    by signer index.
  - participant_list, a set containing identifiers for each signer, similarly of length
    NUM_SIGNERS (sent by the Coordinator).

  Outputs: a signature share sig_share and commitment share comm_share, which
           are Scalar and Element values respectively.

  def sign(index, sk, group_public_key, nonce, comm, msg, commitment_list, participant_list):
    # Compute the binding factor
    encoded_commitments = encode_group_commitment_list(commitment_list)
    msg_hash = H3(msg)
    binding_factor = H1(encoded_commitments || msg_hash)

    # Compute the group commitment
    R = G.Identity()
    for (_, hiding_nonce_commitment, binding_nonce_commitment) in commitment_list:
      R = R + (hiding_nonce_commitment + (binding_nonce_commitment * binding_factor))

    lambda_i = derive_lagrange_coefficient(index, participant_list)

    # Compute the per-message challenge
    msg_hash = H3(msg)
    group_comm_enc = G.SerializeElement(R)
    group_public_key_enc = G.SerializeElement(group_public_key)
    challenge_input = group_comm_enc || group_public_key_enc || msg_hash
    c = H2(challenge_input)

    # Compute the signature share
    (hiding_nonce, binding_nonce) = nonce_i
    sig_share = hiding_nonce + (binding_nonce * binding_factor) + (lambda_i * sk_i * c)

    # Compute the commitment share
    (hiding_nonce_commitment, binding_nonce_commitment) = comm_i
    comm_share = hiding_nonce_commitment + (binding_nonce_commitment * binding_factor)

    return sig_share, comm_share
~~~

The output of this procedure is a signature share and group commitment share.
Each signer then sends these shares back to the collector; see
{{encode-sig-share}} for encoding recommendations.

The Coordinator MUST verify the set of signature shares using the following procedure.

<!-- the inputs to this function need to be revisited, things can probably be made simpler -->
~~~
  Inputs:
  - index, Index `i` of the signer. Note index will never equal `0`.
  - PK, the public key for the group
  - PK_i, the public key for the ith signer, where PK_i = ScalarBaseMult(s[i])
  - sig_share, the signature share for the ith signer, computed from the signer
  - comm_share, the commitment for the ith signer, computed from the signer
  - R, the group commitment
  - msg, the message to be signed
  - participant_list, a set containing identifiers for each signer, similarly of length
    NUM_SIGNERS (sent by the Coordinator).

  Outputs: 1 if the signature share is valid, and 0 otherwise.

  def verify_signature_share(index, PK, PK_i, sig_share, comm_share, R, msg, participant_list):
    msg_hash = H3(msg)
    group_comm_enc = G.SerializeElement(R)
    group_public_key_enc = G.SerializeElement(group_public_key)
    challenge_input = group_comm_enc || group_public_key_enc || msg_hash
    c = H2(challenge_input)

    l = G.ScalarbaseMult(sig_share)

    lambda_i = derive_lagrange_coefficient(index, participant_list)
    r = comm_share + (sig_share * c * lambda_i)

    return l == r
~~~

## Signature Share Aggregation {#frost-aggregation}

After signers perform round two and send their signature shares to the Coordinator,
the Coordinator performs the `aggregate` operation and publishes the resulting
signature. Note that here we do not specify the Coordinator as validating each
signature schare, as if any signature share is invalid, the resulting joint
signature will similarly be invalid. Deployments that wish to validate signature
shares can do so using the `verify_signature_share` function in {{frost-round-two}}

~~~
  Inputs:
  - R: the group commitment.
  - sig_shares: a set of signature shares z_i for each signer, of length NUM_SIGNERS,
  where THRESHOLD_LIMIT <= NUM_SIGNERS <= MAX_SIGNERS.

  Outputs: (R, z), a Schnorr signature consisting of an Element and Scalar value.

  def frost_aggregate(R, sig_shares):
    z = 0
    for z_i in sig_shares:
      z = z + z_i
    return (R, z)
~~~

# Ciphersuites {#ciphersuites}

A FROST ciphersuite must specify the underlying prime-order group details
and cryptographic hash function. Each ciphersuite is denoted as (Group, Hash),
e.g., (ristretto255, SHA-512). This section contains some ciphersuites.
The RECOMMENDED ciphersuite is (ristretto255, SHA-512) {{recommended-suite}}.
The (edwards25519, SHA-512) ciphersuite is included for backwards compatibility
with {{!RFC8032}}.

## FROST(edwards25519, SHA-512)

This ciphersuite uses edwards25519 for the Group and SHA-512 for the Hash function `H`
meant to produce signatures indistinguishable from Ed25519 as specified in {{!RFC8032}}.
The value of the contextString parameter is empty.

- Group: ed25519 {{!RFC8032}}
  - SerializeElement: Implemented as specified in {{!RFC8032, Section 5.1.2}}.
  - DeserializeElement: Implemented as specified in {{!RFC8032, Section 5.1.3}}.
- Hash (`H`): SHA-512, and Nh = 64.
  - H1(m): Implemented by computing H("rho" || m), interpreting the lower
    32 bytes as a little-endian integer, and reducing the resulting integer modulo
    L = 2^252+27742317777372353535851937790883648493.
  - H2(m): Implemented by computing H(m), interpreting the lower 32 bytes
    as a little-endian integer, and reducing the resulting integer modulo
    L = 2^252+27742317777372353535851937790883648493.
  - H3(m): Implemented as an alias for H, i.e., H(m).

Normally H2 would also include a domain separator, but for backwards compatibility
with {{!RFC8032}}, it is omitted.

## FROST(ristretto255, SHA-512) {#recommended-suite}

This ciphersuite uses ristretto255 for the Group and SHA-512 for the Hash function `H`.
The value of the contextString parameter is "FROST-RISTRETTO255-SHA512".

- Group: ristretto255 {{!RISTRETTO=I-D.irtf-cfrg-ristretto255-decaf448}}
  - SerializeElement: Implemented using the 'Encode' function from {{!RISTRETTO}}.
  - DeserializElement: Implemented using the 'Decode' function from {{!RISTRETTO}}.
- Hash (`H`): SHA-512, and Nh = 64.
  - H1(m): Implemented by computing H(contextString || "rho" || m) and mapping the
    the output to a Scalar as described in {{!RISTRETTO, Section 4.4}}.
  - H2(m): Implemented by computing H(contextString || "chal" || m) and mapping the
    the output to a Scalar as described in {{!RISTRETTO, Section 4.4}}.
  - H3(m): Implemented by computing H(contextString \|\| "digest" \|\| m).

## FROST(P-256, SHA-256)

This ciphersuite uses P-256 for the Group and SHA-256 for the Hash function `H`.
The value of the contextString parameter is "FROST-P256-SHA256".

- Group: P-256 (secp256r1) {{x9.62}}
  - SerializeElement: Implemented using the compressed Elliptic-Curve-Point-to-Octet-String
    method according to {{SECG}}.
  - DeserializeElement: Implemented by attempting to deserialize a public key using
    the compressed Octet-String-to-Elliptic-Curve-Point method according to {{SECG}},
    and then performs partial public-key validation as defined in section 5.6.2.3.4 of
    {{!KEYAGREEMENT=DOI.10.6028/NIST.SP.800-56Ar3}}.
  - Serialization: Elements are serialized as Ne = 33 byte string
- Hash (`H`): SHA-256, and Nh = 32.
  - H1(m): Implemented using hash_to_field from {{!HASH-TO-CURVE=I-D.irtf-cfrg-hash-to-curve, Section 5.3}}
    using L = 48, `expand_message_xmd` with SHA-256, DST = contextString || "rho", and
    prime modulus equal to `Order()`.
  - H2(m): Implemented using hash_to_field from {{!HASH-TO-CURVE, Section 5.3}}
    using L = 48, `expand_message_xmd` with SHA-256, DST = contextString || "chal", and
    prime modulus equal to `Order()`.
  - H3(m): Implemented by computing H(contextString \|\| "digest" \|\| m).

# Security Considerations {#sec-considerations}

A security analysis of FROST exists in {{FROST20}}. The protocol as specified
in this document assumes the following threat model.

* Trusted dealer. The dealer that performs key generation is trusted to follow
the protocol, although participants still are able to verify the consistency of their
shares via a VSS (verifiable secret sharing) step; see {{dep-vss}}.

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

# Removing the Coordinator Role

In some settings, it may be desirable to omit the role of the coordinator entirely.
Doing so does not change the security implications of FROST, but instead simply
requires each participant to communicate with all other participants. We loosely
describe how to perform FROST signing among signers without this coordinator role.
We assume that every participant receives as input from an external source the
message to be signed prior to performing the protocol.

Every participant begins by performing `frost_commit()` as is done in the setting
where a coordinator is used. However, instead of sending the commitment
`SigningCommitment` to the coordinator, every participant instead will publish
this commitment to every other participant. Then, in the second round, instead of
receiving a `SigningPackage` from the coordinator, signers will already have
sufficient information to perform signing. They will directly perform `frost_sign`.
All participants will then publish a `SignatureShare` to one another. After having
received all signature shares from all other signers, each signer will then perform
`frost_verify` and then `frost_aggregate` directly.

The requirements for the underlying network channel remain the same in the setting
where all participants play the role of the coordinator, in that all messages that
are exchanged are public and so the channel simply must be reliable. However, in
the setting that a player attempts to split the view of all other players by
sending disjoint values to a subset of players, the signing operation will output
an invalid signature. To avoid this denial of service, implementations may wish
to define a mechanism where messages are authenticated, so that cheating players
can be identified and excluded.

# Contributors

* Isis Lovecruft
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
  Inputs:
  - n, the number of shares to generate, an integer
  - t, the threshold of the secret sharing scheme, an integer

  Outputs: a secret key Scalar, public key Element, along with `n`
  shares of the secret key, each a Scalar value.

  def trusted_dealer_keygen(n, t):
    secret_key = G.RandomScalar()
    secret_key_shares = secret_share_split(secret_key, n, t)
    public_key = G.ScalarBaseMult(s)
    return secret_key, public_key, secret_key_shares
~~~

It is assumed the dealer then sends one secret key to each of the NUM_SIGNERS participants,
and afterwards deletes the secrets from their local device.

Use of this method for key generation requires a mutually authenticated secure channel
between Coordinator and participants, wherein the channel provides confidentiality
and integrity. Mutually authenticated TLS is one possible deployment option.

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

    # Generate random coefficients for the polynomial, yielding
    # a polynomial of degree (t - 1)
    coefficients = [s]
    for i in range(t - 1):
      coefficients.append(RandomScalar())

    # Evaluate the polynomial for each point x=1,...,n
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
`i` MUST never equal `0`.

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

# Wire Format {#wire-format}

Applications are responsible for encoding protocol messages between peers. This section
contains RECOMMENDED encodings for different protocol messages as described in {{frost-spec}}.

## Signing Commitment {#encode-commitment}

A commitment from a signer is a pair of Element values. It can be encoded in the following manner.

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
: The commitment binding factor encoded as a serialized group element.

## Signing Packages {#encode-package}

The Coordinator sends "signing packages" to each Signer in Round two. Each package
contains the list of signing commitments generated during round one along with the
message to sign. This package can be encoded in the following manner.

~~~
struct {
  SigningCommitment signing_commitments<1..2^16-1>;
  opaque msg<0..2^16-1>;
} SigningPackage;
~~~

signing_commitments
: An list of SIGNING_COUNT SigningCommitment values, where THRESHOLD_LIIMT <= SIGNING_COUNT <= NUM_SIGNERS,
ordered in ascending order by SigningCommitment.id. This list MUST NOT contain more than one
SigningCommitment value corresponding to each signer. Signers MUST ignore SigningPackage values with
duplicate SignerIDs. <!-- this requirement should move to the main body of the spec -->

msg
: The message to be signed.

## Signature Share {#encode-sig-share}

The output of each signer is a signature share which is sent to the Coordinator. This
can be constructed as follows.

~~~
  struct {
    SignerID id;
    opaque signature_share[Ns];
    opaque commitment_share[Ne];
  } SignatureShare;
~~~

id
: The SignerID.

signature_share
: The signature share from this signer encoded as a serialized scalar.

# Test Vectors

This section contains test vectors for all ciphersuites listed in {{ciphersuites}}.
All Element and Scalar values are represented in serialized form and encoded in
hexadecimal strings. Signatures are represented as the concatenation of their
constituent parts. The input message to be signed is also encoded as a hexadecimal
string.

Each test vector consists of the following information.

- Configuration: This lists the fixed parameters for the particular instantiation
  of FROST, including MAX_SIGNERS, THRESHOLD_LIMIT, and NUM_SIGNERS.
- Group input parameters: This lists the group secret key and shared public key,
  generated by a trusted dealer as described in {{dep-dealer}}, as well as the
  input message to be signed. All values are encoded as hexadecimal strings.
- Signer input parameters: This lists the signing key share for each of the
  NUM_SIGNERS signers.
- Round one parameters and outputs: This lists the NUM_SIGNERS participants engaged
  in the protocol, identified by their integer index, the hiding and binding commitment
  values produced in {{frost-round-one}}, as well as the resulting group commitment list,
  encoded as described in {{dep-encoding}}, and group binding factor as computed in {{frost-round-two}}).
- Round two parameters and outputs: This lists the NUM_SIGNERS participants engaged
  in the protocol, identified by their integer index, along with their corresponding
  output signature share and group commitment share as produced in {{frost-round-two}}.
- Final output: This lists the aggregate signature as produced in {{frost-aggregation}}.

## FROST(Ed25519, SHA512)

~~~
// Configuration information
MAX_SIGNERS: 3
THRESHOLD_LIMIT: 2
NUM_SIGNERS: 2

// Group input parameters
group_secret_key: 7c1c33d3f5291d85de664833beb1ad469f7fb6025a0ec78b3a7
90c6e13a98304
group_public_key: 377a6acb3b9b5f642c5ce355d23cac0568aad0da63c633d59d4
168bdcbce35af
message: 74657374

// Signer input parameters
S1 signer_share: 949dcc590407aae7d388761cddb0c0db6f5627aea8e217f4a033
f2ec83d93509
S2 signer_share: ac1e66e012e4364ac9aaa405fcafd370402d9859f7b6685c07ee
d76bf409e80d
S3 signer_share: d7cb090a075eb154e82fdb4b3cb507f110040905468bb9c46da8
bdea643a9a02

// Round one parameters
participants: 1,2
commitment_list: 000178e175d15cb5cec1257e0d84d797ba8c3dd9b4c7bc50f3fa
527c200bcc6c4a954cdad16ae67ac5919159d655b681bd038574383bab423614f8967
396ee12ca62000288a4e6c3d8353dc3f4aca2e10d10a75fb98d9fbea98981bfb25375
996c5767c932bbf10c41feb17d41cc6433e69f16cceccc42a00aedf72feb5f44929fd
f2e2fee26b0dd4af7e749aa1a8ee3c10ae9923f618980772e473f8819a5d4940e0db2
7ac185f8a0e1d5f84f88bc887fd67b143732c304cc5fa9ad8e6f57f50028a8ff
group_binding_factor: c4d7668d793ff4c6ec424fb493cdab3ef5b625eefffe775
71ff28a345e5f700a

// Signer round one outputs
S1 hiding_nonce: 570f27bfd808ade115a701eeee997a488662bca8c2a073143e66
2318f1ed8308
S1 binding_nonce: 6720f0436bd135fe8dddc3fadd6e0d13dbd58a1981e587d377d
48e0b8f1c3c01
S1 hiding_nonce_commitment: 78e175d15cb5cec1257e0d84d797ba8c3dd9b4c7b
c50f3fa527c200bcc6c4a95
S1 binding_nonce_commitment: 4cdad16ae67ac5919159d655b681bd038574383b
ab423614f8967396ee12ca62
S2 hiding_nonce: 2a67c5e85884d0275a7a740ba8f53617527148418797345071dd
cf1a1bd37206
S2 binding_nonce: a0609158eeb448abe5b0df27f5ece96196df5722c01a999e8a4
5d2d5dfc5620c
S2 hiding_nonce_commitment: 88a4e6c3d8353dc3f4aca2e10d10a75fb98d9fbea
98981bfb25375996c5767c9
S2 binding_nonce_commitment: 32bbf10c41feb17d41cc6433e69f16cceccc42a0
0aedf72feb5f44929fdf2e2f

// Round two parameters
participants: 1,2

// Signer round two outputs
S1 sig_share: f8bbaf924e1c90e11dec1eb679194aade084f92fbf52fdd436ba0a0
7f71ab708
S1 group_commitment_share: 11bb9777aa393b92e814e415039adf62687a0be543
c2322d817e4934bc5a7cf2
S2 sig_share: 80f589405714ca0e6adc87c2c0186a0ae4d6e352f7b248b23149a5d
cd3fe4704
S2 group_commitment_share: 4af85179d17ed031b767ab579e59c7018dac09ae40
0b1700623d0af1129a9c55

sig: ebe7efbb42c4b1c55106b5536fb5e9ac7a6d0803ea4ae9c8c629ca51e05c230e
78b139d3a5305af087c8a6783a32b4b7c45bdd82b60546876803b0e3ca19ff0c
~~~
## FROST(ristretto255, SHA512)

~~~
// Configuration information
MAX_SIGNERS: 3
THRESHOLD_LIMIT: 2
NUM_SIGNERS: 2

// Group input parameters
group_secret_key: ca8009d372fa61174ae16d422a216ff503eccfe12348a5a2e4b
30e95fdd92909
group_public_key: 6acc470751d8954bc4bf3581c3f0d25d4d65ef818318de89f95
00d288d8dcf05
message: 74657374

// Signer input parameters
S1 signer_share: 1767555c694baffbb51ed5e75e3c199f35d025a7a0b40124d93d
6dc824cf240d
S2 signer_share: 7779ab884539ea874bbf44eab45de43367b47b6c1d215ea5cdc7
cbfb4bc41f01
S3 signer_share: c45ff7113c8a376cb7fcab8fe9788edd9898d1319a8dba26c251
2a2f73b91a05

// Round one parameters
participants: 1,2
commitment_list: 00013294581c296781c6fdb2696b2a8d08f961311e15b4bc3614
daec6a19a78cd77a42a3cfa235deb33e7f99a21f4e22b7090d9c278f2613664dff607
115cecedf58000208659fe4a31c1775caa4488f669324460b5d972df8983a6cf8e624
f79906a639285fd985bb44d53b28b6523aa1c459a94bface28ab2f4fcdbc5215df5d9
be234f226c1530c93fbfe1a29f34aa2e13da14ace01b6e6412e36d5e01baba2c78e49
21dc1c0b7143210bb0fc42553c3a9490ba011e30250727c0189372a38632591f
group_binding_factor: 190c206d7368cc7cdf8539680f45a82836889db034464d9
f9cc13c970fc9d20e

// Signer round one outputs
S1 hiding_nonce: 7e119fcff436f4817fbcd1b09e82d7d2ff6dd433b0f81e012cad
d4662282b809
S1 binding_nonce: 3b3bbe82babf2a67ded81b308ba45f73b88f6cf3f6aaa444225
6b7a0a6a9e20c
S1 hiding_nonce_commitment: 3294581c296781c6fdb2696b2a8d08f961311e15b
4bc3614daec6a19a78cd77a
S1 binding_nonce_commitment: 42a3cfa235deb33e7f99a21f4e22b7090d9c278f
2613664dff607115cecedf58
S2 hiding_nonce: 488cfde0a2bba98ba4c3e65645e1b77386eb4063e497801fbbbd
112ad1f7d708
S2 binding_nonce: f33b7cd25041000d7935823cb0c99503afac2860b1c099435eb
472bb29329e02
S2 hiding_nonce_commitment: 08659fe4a31c1775caa4488f669324460b5d972df
8983a6cf8e624f79906a639
S2 binding_nonce_commitment: 285fd985bb44d53b28b6523aa1c459a94bface28
ab2f4fcdbc5215df5d9be234

// Round two parameters
participants: 1,2

// Signer round two outputs
S1 sig_share: 0f03834e01fc2447135f694a5d1d6493f7a21fcf6fc41191118000e
8b9a29306
S1 group_commitment_share: 76818272e9bd5d71f062dce08687919850aaf4b8cf
d135ad70e50e0267d87246
S2 sig_share: 08442979523a3e335cf4c03fe58cdcec25841e64f5a4f2ac656730c
1fee43509
S2 group_commitment_share: 62e97479cb0df12293aadfa88e5d1caa7f82d548f7
7eaa2408fe4bca61916439

sig: 56604a3b6ca135e56f5d68d2f6496e3e0e9b9ec691a3790f5e8311d24d75ce13
1747acc75336637a6f532a8a42aa40801d273e336569043e77e730a9b887c90f
~~~
## FROST(P-256, SHA256)

~~~
// Configuration information
MAX_SIGNERS: 3
THRESHOLD_LIMIT: 2
NUM_SIGNERS: 2

// Group input parameters
group_secret_key: 949cbef2af8f2ab1565b67c4a98c456089755e4b20be20b09cc
49a943b20e293
group_public_key: 026368c1d8eb8da1b95bcfc10b8b1d01d87730299c92870b640
4178ae0ce91a4ac
message: 74657374

// Signer input parameters
S1 signer_share: cc70526752b166b47cb72c2f4177c7795d348c9f606c74421107
8152577f001d
S2 signer_share: 0443e5dcf5d3a2b6a312f099d9634992740cc045f903294e9190
9d4d7779f856
S3 signer_share: 3c17795198f5deb9c96eb504714ecbab47cbee9a38b17ce005d3
840b93d815e0

// Round one parameters
participants: 1,2
commitment_list: 000102d672c0206c0f0500c00db74a6d743e58a65bdc601a1fd2
8cae91d895b5cfbb6702f82b18a80d1b0a2a29f70d5caaf80e31d7277b2e7503fded0
fcc42987ffeb9a000020263625b86d512f22fcf327f3b9f451fa146d7d5cceb576a32
cb36174cae57971d03dac43c989f56425601215cd269640a293b51544f602b29528cd
6cad937d1642fbce8e9dd076882537d47858b7ed704e0029ea004fbeb28a46d1ba698
cc0099a3
group_binding_factor: 1f26a9814df6c8664875bb072d7dbcf367a462ec982e19a
d5893d2e5ef4cf00e

// Signer round one outputs
S1 hiding_nonce: baa1a30522fb9361ff76b1402d9b5614e5da3c4ba5b0e743afa4
ffd0b7a98245
S1 binding_nonce: 0b58e879921d3abf89ac90834916d4e31ac522d7ad8e498cd53
201e139ee496f
S1 hiding_nonce_commitment: 02d672c0206c0f0500c00db74a6d743e58a65bdc6
01a1fd28cae91d895b5cfbb67
S1 binding_nonce_commitment: 02f82b18a80d1b0a2a29f70d5caaf80e31d7277b
2e7503fded0fcc42987ffeb9a0
S2 hiding_nonce: c26f9bebe769f1d3ac629b19090bd6c657a7085ff79d61cf9074
1b354fc5a50a
S2 binding_nonce: 896026a3615233a6f9a359456fb5d6f7871d4a46b83b9b3336f
b783576e801c6
S2 hiding_nonce_commitment: 0263625b86d512f22fcf327f3b9f451fa146d7d5c
ceb576a32cb36174cae57971d
S2 binding_nonce_commitment: 03dac43c989f56425601215cd269640a293b5154
4f602b29528cd6cad937d1642f

// Round two parameters
participants: 1,2

// Signer round two outputs
S1 sig_share: 4c0d3c95be8895192f97958c31875e4743f647a5ae0d3ffc7c22948
b2ba879ec
S1 group_commitment_share: 02794fb94cd7b4009aa30888ab90e1bba6b4f60d7d
9e550ba83421cffe179498ff
S2 sig_share: 5c4df264448a57f501d34236e04039df56aa84ef4d90c3040bbf6b4
d5ff0fa59
S2 group_commitment_share: 024e8a66e7c565b72c3e5f423a73921353371ce0c7
48ca5325771119776d5019f5

sig: 03bf586eabe39ca2c49a6b46262b072c3da3945c72dc63278c887cf975fcf329
8aa85b2efa0312ed0e316ad7c311c798269aa0cc94fb9e030087e1ffd88b997445
~~~
