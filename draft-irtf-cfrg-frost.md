---
title: "Two-Round FROST with Trusted Dealer"
abbrev: "FROST"
docname: draft-irtf-cfrg-frost-00
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
 -  ins: D. Connelly
    name: Deirdre Connelly
    organization: Zcash Foundation
    email: durumcrustulum@gmail.com
 -  ins: T. Wilson-Brown
    name: T Wilson-Brown
    organization: Zcash Foundation
    email: teor@riseup.net

informative:
  frost:
    target: https://eprint.iacr.org/2020/852.pdf
    title: "Two-Round FROST with Trusted Dealer"
    author:
      - name: Chelsea Komlo
      - name: Ian Goldberg
      - name: Deirdre Connelly
      - name: T Wilson-Brown
    date: 2021-06-01



--- abstract

In this draft, we present a variant of FROST, a Flexible Round-Optimized Schnorr Threshold
signature scheme. FROST signatures can be issued after a threshold number of entities
cooperate to issue a signature, allowing for improved distribution of trust and
redundancy with respect to a secret key.
This variant of FROST specifically defines key generation as performed by a trusted dealer
and signing as a two-round protocol.
Finally, this draft specifies signatures that are compatible with EdDSA verification of
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

This draft specifies the variant of FROST that requires a trusted dealer to perform
key generation. Further, this draft specifies only two-round signing operations.
This draft specifies signatures that are compatible with EdDSA verification of
signatures, bui not EdDSA nonce generation. EdDSA-style nonce-generation, where the
nonce is derived deterministically, is insecure in a multi-party signature setting.

# Change Log

draft-01

- Submitted a draft that specifies notation and cryptographic dependencies,
as well including additional authors.

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

- Trusted dealer: Entity responsible for driving distributed key generation
  for signers.
- Signers: Entities with signing key shares that participate in the threshold
  signing protocol
- Signature aggregator: A Signer that combines multiple signatures into a single,
  aggregate signature under the group public key.

FROST assumes the selection of participants, including the dealer, signer, and
aggregator are all chosen external to the protocol.

FROST consists of two protocols: distributed key generation (DKG) and threshold
signing. These are briefly described in the following sections.

## Trusted Dealer Key Generation Overview

In the DKG protocol, every Signer participant contributes equally to
the generation of the shared secret. The output of the protocol is (1) a shared,
group public key PK owned by each Signer, and (2) individual shares of the signing
key owned by each Signer. This protocol assumes an authenticated, confidential, and
reliable channel between all participants. Specifically, the dealer must be able to
transmit secret key material to each participant over this channel.

## Signing Overview

In the threshold signing protocol, Signers participate in multiple exchanges
to sign an input message and produce a single, aggregate signature. This protocol
assumes a reliable channel. While messages that are exchanged contain no secret
information, the channel must be able to deliver messages reliably in order for
the protocol to complete.

# Conventions and Terminology

The following notation and terminology are used throughout this document.

* `s` denotes a secret that is Shamir secret shared among the participants.
* `s_i` denotes the ith share of the secret `s`.
* A participant is an entity that is trusted to hold a secret share.
* `n` denotes the number of participants, and the number of shares that `s` is split into.
* `t` denotes the threshold number of participants required to issue a signature. More specifically,
at least `t` shares must be combined to issue a valid signature.
* `C` represents the coalition of signers, and is a set of participant identifiers of size at least `t`.
* `L_i` represents the ith Lagrange coefficient.
* `sig = (R, z)` denotes a Schnorr signature with public commitment `R` and response `z`.
* `PK` is the group public key.
* `sk_i` is each ith individual's private key.

This specification makes use of the following utility functions:

* SUM(START, END){TERMS}: this function denotes the summation from START to END
  (inclusive) of TERMS. For example, SUM(N=0, 3){2N} is equal to 2*(1+2+3)=12.
* PROD(START, END){TERMS}: this function denotes the product from START to
  END of TERMS in similar manner.

Unless otherwise stated, we assume that secrets are sampled uniformly at random
using a cryptographically secure pseudorandom number generator (CSPRNG); see
{{?RFC4086}} for additional guidance on the generation of random numbers.

# Cryptographic Dependencies

FROST depends on the following constructs:

- Prime-Order Group, {{dep-pog}};
- Cryptographic hash function, {{dep-hash}};
- EdDSA signature scheme, {{dep-sigs}}; and
- Polynomial Operations, {#dep-polynomial}
- Shamir Secret Sharing, {#dep-shamir}
- Verifiable Secret Sharing committments, {{dep-vss}}.

These are described in the following sections.

## Prime-Order Group {#dep-pog}

FROST depends on an abelian group `G` of prime order `p`. The fundamental group operation
is addition `+` with identity element `I`. For any elements `A` and `B` of the group `G`,
`A + B = B + A` is also a member of `G`. Also, for any `A` in `GG`, there exists an element
`-A` such that `A + (-A) = (-A) + A = I`. Scalar multiplication is equivalent to the repeated
application of the group operation on an element A with itself `r-1` times, this is denoted
as `r*A = A + ... + A`. For any element `A`, `p * A = I`. We denote `B` as the fixed generator
of the group. Scalar base multiplication is equivalent to the repeated application of the group
operation `G` with itself `r-1` times, this is denoted as `ScalarBaseMult(r)`. The set of
scalars corresponds to `GF(p)`, which refer to as the scalar field. This document uses types
`Element` and `Scalar` to denote elements of the group `G` and its set of scalars, respectively.

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
- DeserializeScalar(buf): A member function of `GG` that maps a byte array
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
little-endian integer, is a valud between 0 and `Order()`.

## Cryptographic Hash Function {#dep-hash}

FROST requires the use of a cryptographically secure hash function, generically
written as H, which functions effectively as a random oracle. For concrete
recommendations on hash functions which SHOULD BE used in practice, see
{{ciphersuites}}.


TODO: writeme

## EdDSA Signatures {#dep-sigs}

Verifying an EdDSA signature `sig` over message `msg` with public key `PK` is
done as follows.

~~~
EdDSA_verify(msg, sig, PK)

Inputs:
- msg, message signed, an octet string
- sig, message signature, a tuple of scalars (z, c)
- PK, EdDSA public key

Outputs: 1 if the signature is valid, and 0 otherwise

def EdDSA_verify(msg, sig, PK):
  (z, c) = SIG
  R' = (z * P) + (PK * c^-1)
  c' = Hash(m, R')
  if c = c':
    return 1
  return 0
~~~

## Polynomial Operations {#dep-polynomial}

(Dan Shumow will write this section)

  * Evaluation of a polynomial at a specific point, "polynomial_evaluate", which takes as input the x-value and the polynomial coefficients

    - Horner's method

  * Derivation of the ith Lagrange coefficient, "polynomial_interpolation", which takes as input the coefficient and then set of remaining points


## Shamir Secret Sharing {#dep-shamir}

In Shamir secret sharing, a dealer distributes a secret `s` to `n` participants
in such a way that any cooperating subset of `t` participants can recover the
secret. There are two basic steps in this scheme: (1) splitting a secret into
multiple shares, and (2) combining shares to reveal the resulting secret.

This secret sharing scheme works over any field F. In this specification, F is
the scalar field of the prime-order group G. For convenience, we assume F has
a member function called `random_element` which returns a uniformly random
element in the field.

[OPEN ISSUE: should `s` be assume a member of F, or should this procedure encode the secret as an element of F?]

The procedure for splitting a secret into shares is as follows:

~~~
secret_share_split(s, n, t)

Inputs:
- s, secret to be shared, an element of F
- n, the number of shares to generate, an integer
- t, the threshold of the secret sharing scheme, an integer

Outputs: a list of n secret shares, each of which is an element of F

Errors:
- "invalid parameters", if t > n

def secret_share(s, n, t):
  if t > n:
    raise "invalid parameters"

  # Generate random coefficients for the polynomial
  coefficients = [s]
  for i in range(t - 1):
    coefficients.append(F.random_element())

  # Evaluate the polynomial for each participant, identified by their index i
  points = []
  for i in range(n):
    point_i = polynomial_evaluate(1, coefficients)
    points.append(point_i)
  return points
~~~

Let `points` be the output of this function. The i-th element in `points` is
the share for the i-th participant, which is funtionally the randomly generated
polynomial evaluated at `i`. We denote a secret share as the tuple `(i, points[i])`,
and the list of these shares as `shares`.

The procedure for combining a `shares` list of length `t` to recover the
secret `s` is as follows:

~~~
secret_share_combine(shares)

Inputs:
- shares, a list of t secret shares, each a tuple (i, f(i))
- n, the number of shares to generate, an integer
- t, the threshold of the secret sharing scheme, an integer

Outputs: a list of n secret shares, each of which is an element of F

Errors:
- "XXX", TBD

def secret_share_combine(shares):
  s = polynomial_interpolation(0, shares)
  return s
~~~

## Verifiable Secret Sharing {#dep-vss}

Feldman's Verifiable Secret Sharing (VSS)
builds upon Shamir secret sharing, adding a verification step to
demonstrate the consistency of a participant's share with a public
commitment which all participants are assumed to hold a consistent view of.
To validate that a share is well formed,
each
participant validates their share using this commitment.
If the validation
fails, the participant can issue a complaint against the dealer, and
take actions such as broadcasting this complaint to all other participants.

TODO describe the math

# Two-Round FROST

The FROST protocol assumes that each participant `P_i` knows the following:

- Group public key, denoted `PK = s * B`, corresponding to the group secret key `s`
- Participant signing key, which is a secret share `(i, s[i])`, where `s[i]` is the i-th secret share of `s`

The exact key generation mechanism is out of scope for this specification. One
possible mechanism is to depend on a trust dealer, wherein the dealer generates
a group secret `s` uniformly at random and uses Verifiable Secret Sharing to share
it with each participant. Another mechanism is to use a distributed key generation
protocol.

The rest of this section describes the core FROST protocol.

## Signing

Chelsea will write this

# Curve and Verification Compatability

Deirdre will write this.

* EdDSA over edwards25519 (RFC 8032)

* EdDSA over Ristretto

# Recommended Ciphersuites {#ciphersuites}

TODO: writeme

# Security Considerations

* Trusted dealer. The dealer that performs key generation is trusted to follow
the protocol, although participants still are able to verify the consistency of their
shares via a VSS (verifiable secret sharing) step.
* Unforgeability assuming less than `(t-1)` corrupted signers. So long as an adverary
corrupts fewer than `t-1` participants, the scheme remains secure against EUF-CMA attacks.
* Protection against key-recovery attacks. Nonces generated by each participant in the
first round of signing must be sampled uniformly at random and cannot be derived from some
determinstic function. This is to avoid replay attacks initiated by other signers, which
allows for a complete key-recovery attack.

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

--- back

# Acknowledgments
{:numbered="false"}

TODO acknowledge.
