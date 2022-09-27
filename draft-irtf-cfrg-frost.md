---
title: "Two-Round Threshold Schnorr Signatures with FROST"
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
    date: Nov, 2005
    seriesinfo:
      "ANS": X9.62-2005
    author:
      -
        org: ANS
  SEC1:
    title: "Elliptic Curve Cryptography, Standards for Efficient Cryptography Group, ver. 2"
    target: https://secg.org/sec1-v2.pdf
    date: 2009
  SEC2:
    title: "Recommended Elliptic Curve Domain Parameters, Standards for Efficient Cryptography Group, ver. 2"
    target: https://secg.org/sec2-v2.pdf
    date: 2010
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
  StrongerSec22:
    target: https://eprint.iacr.org/2022/833
    title: "Stronger Security for Non-Interactive Threshold Signatures: BLS and FROST"
    author:
      - name: Mihir Bellare
      - name: Stefano Tessaro
      - name: Chenzhi Zhu
    date: 2022-06-01
  BonehShoup:
    target: http://toc.cryptobook.us/book.pdf
    title: "A Graduate Course in Applied Cryptography"
    author:
      - name: Dan Boneh
      - name: Victor Shoup
    date: 2020-01

--- abstract

In this draft, we present the two-round signing variant of FROST, a Flexible Round-Optimized
Schnorr Threshold signature scheme. FROST signatures can be issued after a threshold number
of entities cooperate to issue a signature, allowing for improved distribution of trust and
redundancy with respect to a secret key. Further, this draft specifies signatures that are
compatible with {{!RFC8032}}. However, unlike {{!RFC8032}}, the protocol for producing
signatures in this draft is not deterministic, so as to ensure protection against a
key-recovery attack that is possible when even only one signer participant is malicious.

--- middle

# Introduction

DISCLAIMER: This is a work-in-progress draft of FROST.

RFC EDITOR: PLEASE REMOVE THE FOLLOWING PARAGRAPH The source for this draft is
maintained in GitHub. Suggested changes should be submitted as pull requests
at https://github.com/cfrg/draft-irtf-cfrg-frost. Instructions are on that page as
well.

Unlike signatures in a single-party setting, threshold signatures
require cooperation among a threshold number of signing participants each holding a share
of a common private key. The security of threshold schemes in general assumes
that an adversary can corrupt strictly fewer than a threshold number of signer participants.

This document presents a variant of a Flexible Round-Optimized Schnorr Threshold (FROST)
signature scheme originally defined in {{FROST20}}. FROST reduces network overhead during
threshold signing operations while employing a novel technique to protect against forgery
attacks applicable to prior Schnorr-based threshold signature constructions. The variant of
FROST presented in this document requires two rounds to compute a signature. Single-round
signing with FROST is out of scope.

For select ciphersuites, the signatures produced by this draft are compatible with
{{!RFC8032}}. However, unlike {{!RFC8032}}, signatures produced by FROST are not
deterministic, since deriving nonces deterministically allows for a complete key-recovery
attack in multi-party discrete logarithm-based signatures, such as FROST.

While an optimization to FROST was shown in {{Schnorr21}} that reduces scalar multiplications
from linear in the number of signing participants to constant, this draft does not specify that optimization
due to the malleability that this optimization introduces, as shown in {{StrongerSec22}}.
Specifically, this optimization removes the guarantee that the set of signer participants that started
round one of the protocol is the same set of signing participants that produced the signature output by
round two.

Key generation for FROST signing is out of scope for this document. However, for completeness,
key generation with a trusted dealer is specified in {{dep-dealer}}.

## Change Log

draft-10

- Update version string constant (#296)
- Fix some editorial issues from Ian Goldberg (#295)

draft-09

- Add single-signer signature generation to complement RFC8032 functions (#293)
- Address Thomas Pornin review comments from https://mailarchive.ietf.org/arch/msg/crypto-panel/bPyYzwtHlCj00g8YF1tjj-iYP2c/ (#292, #291, #290, #289, #287, #286, #285, #282, #281, #280, #279, #278, #277, #276, #275, #273, #272, #267)
- Correct Ed448 ciphersuite (#246)
- Various editorial changes (#241, #240)

draft-08

- Add notation for Scalar multiplication (#237)
- Add secp2561k1 ciphersuite (#223)
- Remove RandomScalar implementation details (#231)
- Add domain separation for message and commitment digests (#228)

draft-07

- Fix bug in per-rho signer computation (#222)

draft-06

- Make verification a per-ciphersuite functionality (#219)
- Use per-signer values of rho to mitigate protocol malleability (#217)
- Correct prime-order subgroup checks (#215, #211)
- Fix bug in ed25519 ciphersuite description (#205)
- Various editorial improvements (#208, #209, #210, #218)

draft-05

- Update test vectors to include version string (#202, #203)
- Rename THRESHOLD_LIMIT to MIN_PARTICIPANTS (#192)
- Use non-contiguous signers for the test vectors (#187)
- Add more reasoning why the coordinator MUST abort (#183)
- Add a function to generate nonces (#182)
- Add MUST that all participants have the same view of VSS commitment (#174)
- Use THRESHOLD_LIMIT instead of t and MAX_PARTICIPANTS instead of n (#171)
- Specify what the dealer is trusted to do (#166)
- Clarify types of NUM_PARTICIPANTS and THRESHOLD_LIMIT (#165)
- Assert that the network channel used for signing should be authenticated (#163)
- Remove wire format section (#156)
- Update group commitment derivation to have a single scalarmul (#150)
- Use RandomNonzeroScalar for single-party Schnorr example (#148)
- Fix group notation and clarify member functions (#145)
- Update existing implementations table (#136)
- Various editorial improvements (#135, #143, #147, #149, #153, #158, #162, #167, #168, #169, #170, #175, #176, #177, #178, #184, #186, #193, #198, #199)

draft-04

- Added methods to verify VSS commitments and derive group info (#126, #132).
- Changed check for participants to consider only nonnegative numbers (#133).
- Changed sampling for secrets and coefficients to allow the zero element (#130).
- Split test vectors into separate files (#129)
- Update wire structs to remove commitment shares where not necessary (#128)
- Add failure checks (#127)
- Update group info to include each participant's key and clarify how public key material is obtained (#120, #121).
- Define cofactor checks for verification (#118)
- Various editorial improvements and add contributors (#124, #123, #119, #116, #113, #109)

draft-03

- Refactor the second round to use state from the first round (#94).
- Ensure that verification of signature shares from the second round uses commitments from the first round (#94).
- Clarify RFC8032 interoperability based on PureEdDSA (#86).
- Specify signature serialization based on element and scalar serialization (#85).
- Fix hash function domain separation formatting (#83).
- Make trusted dealer key generation deterministic (#104).
- Add additional constraints on participant indexes and nonce usage (#105, #103, #98, #97).
- Apply various editorial improvements.

draft-02

- Fully specify both rounds of FROST, as well as trusted dealer key generation.
- Add ciphersuites and corresponding test vectors, including suites for RFC8032 compatibility.
- Refactor document for editorial clarity.

draft-01

- Specify operations, notation and cryptographic dependencies.

draft-00

- Outline CFRG draft based on draft-komlo-frost.

# Conventions and Definitions

{::boilerplate bcp14}

The following notation is used throughout the document.

* `random_bytes(n)`: Outputs `n` bytes, sampled uniformly at random
using a cryptographically secure pseudorandom number generator (CSPRNG).
* `count(i, L)`: Outputs the number of times the element `i` is represented in the list `L`.
* `len(l)`: Outputs the length of input list `l`, e.g., `len([1,2,3]) = 3)`.
* `reverse(l)`: Outputs the list `l` in reverse order, e.g., `reverse([1,2,3]) = [3,2,1]`.
* `range(a, b)`: Outputs a list of integers from `a` to `b-1` in ascending order, e.g., `range(1, 4) = [1,2,3]`.
* `pow(a, b)`: Outputs the integer result of `a` to the power of `b`, e.g., `pow(2, 3) = 8`.
* \|\| denotes concatenation of byte strings, i.e., `x || y` denotes the byte string `x`, immediately followed by
  the byte string `y`, with no extra separator, yielding `xy`.
* nil denotes an empty byte string.

Unless otherwise stated, we assume that secrets are sampled uniformly at random
using a cryptographically secure pseudorandom number generator (CSPRNG); see
{{?RFC4086}} for additional guidance on the generation of random numbers.

# Cryptographic Dependencies

FROST signing depends on the following cryptographic constructs:

- Prime-order Group, {{dep-pog}};
- Cryptographic hash function, {{dep-hash}};

These are described in the following sections.

## Prime-Order Group {#dep-pog}

FROST depends on an abelian group of prime order `p`. We represent this
group as the object `G` that additionally defines helper functions described below. The group operation
for `G` is addition `+` with identity element `I`. For any elements `A` and `B` of the group `G`,
`A + B = B + A` is also a member of `G`. Also, for any `A` in `G`, there exists an element
`-A` such that `A + (-A) = (-A) + A = I`. For convenience, we use `-` to denote
subtraction, e.g., `A - B = A + (-B)`. Integers, taken modulo the group order `p`, are called
scalars; arithmetic operations on scalars are implicitly performed modulo `p`. Since `p` is prime,
scalars form a finite field. Scalar multiplication is equivalent to the repeated
application of the group operation on an element `A` with itself `r-1` times, denoted as
`ScalarMult(A, r)`. We denote the sum, difference, and product of two scalars using the `+`, `-`,
and `*` operators, respectively. (Note that this means `+` may refer to group element addition or
scalar addition, depending on types of the operands.) For any element `A`, `ScalarMult(A, p) = I`.
We denote `B` as a fixed generator of the group. Scalar base multiplication is equivalent to the repeated application
of the group operation `B` with itself `r-1` times, this is denoted as `ScalarBaseMult(r)`. The set of
scalars corresponds to `GF(p)`, which we refer to as the scalar field. This document uses types
`Element` and `Scalar` to denote elements of the group `G` and its set of scalars, respectively.
We denote Scalar(x) as the conversion of integer input `x` to the corresponding Scalar value with
the same numeric value. For example, Scalar(1) yields a Scalar representing the value 1.
We denote equality comparison as `==` and assignment of values by `=`. Finally, it is assumed that
group element addition, negation, and equality comparisons can be efficiently computed for
arbitrary group elements.

We now detail a number of member functions that can be invoked on `G`.

- Cofactor(): Outputs the cofactor of `G`.
- Order(): Outputs the order of `G` (i.e. `p`).
- Identity(): Outputs the identity `Element` of the group (i.e. `I`).
- RandomScalar(): Outputs a random `Scalar` element in GF(p), i.e., a random scalar in \[0, p - 1\].
- ScalarMult(A, k): Output the scalar multiplication between `Element` `A` and Scalar `k`.
- ScalarBaseMult(k): Output the scalar multiplication between `Scalar` `k` and the group generator `B`.
- SerializeElement(A): Maps an `Element` `A` to a canonical byte array `buf` of fixed length `Ne`.
- DeserializeElement(buf): Attempts to map a byte array `buf` to an `Element` `A`,
  and fails if the input is not the valid canonical byte representation of an element of
  the group. This function can raise a DeserializeError if deserialization fails
  or `A` is the identity element of the group; see {{ciphersuites}} for group-specific
  input validation steps.
- SerializeScalar(s): Maps a Scalar `s` to a canonical byte array `buf` of fixed length `Ns`.
- DeserializeScalar(buf): Attempts to map a byte array `buf` to a `Scalar` `s`.
  This function can raise a DeserializeError if deserialization fails; see
  {{ciphersuites}} for group-specific input validation steps.

Two additional functions, `SerializePrimeOrderElement` and `DeserializePrimeOrderElement`, are provided.
These create a prime order construction out of the provided group, enabling using FROST with groups which
aren't prime order.

- SerializePrimeOrderElement(A): Multiplies an `Element` `A` by the inverse of the group's
cofactor and then maps to a canonical byte array via calling `SerializeElement`. The serialized
element is not guaranteed to be prime order, yet when deserialized with `DeserializePrimeOrderElement`
is guaranteed to become a prime-order equivalent element to the original.
- DeserializePrimeOrderElement(buf): Attempts to map a byte array `buf` to an `Element` `A`,
calling `DeserializeElement` on `buf`. On success, the result `A` is multiplied by the group's
cofactor. If the result is the identity element of the group, a `DeserializeError` is raised.

Both of these functions may be optimized to simply being `SerializeElement` and `DeserializeElement` for
groups whose cofactor is 1.

## Cryptographic Hash Function {#dep-hash}

FROST requires the use of a cryptographically secure hash function, generically
written as H, which functions effectively as a random oracle. For concrete
recommendations on hash functions which SHOULD be used in practice, see
{{ciphersuites}}. Using H, we introduce separate domain-separated hashes,
H1, H2, H3, H4, and H5:

- H1, H2, and H3 map arbitrary byte strings to Scalar elements of the prime-order group scalar field.
- H4 and H5 are aliases for H with distinct domain separators.

The details of H1, H2, H3, H4, and H5 vary based on ciphersuite. See {{ciphersuites}}
for more details about each.

# Helper Functions {#helpers}

Beyond the core dependencies, the protocol in this document depends on the
following helper operations:

- Nonce generation, {{dep-nonces}};
- Polynomial operations, {{dep-polynomial}};
- Encoding operations, {{dep-encoding}};
- Signature binding {{dep-binding-factor}}, group commitment {{dep-group-commit}}, and challenge computation {{dep-sig-challenge}}.

These sections describes these operations in more detail.

## Nonce generation {#dep-nonces}

To hedge against a bad RNG that outputs predictable values, nonces are
generated with the `nonce_generate` function by combining fresh randomness
and with the secret key as input to a domain-separated hash function built
from the ciphersuite hash function `H`. This domain-separated hash function
is denoted `H3`. This function always samples 32 bytes of fresh randomness
to ensure that the probability of nonce reuse is at most 2<sup>-128</sup>
as long as no more than 2<sup>64</sup> signatures are computed by a given
signing participant.

~~~
  nonce_generate(secret):

  Inputs:
  - secret, a Scalar

  Outputs: nonce, a Scalar

  def nonce_generate(secret):
    random_bytes = random_bytes(32)
    secret_enc = G.SerializeScalar(secret)
    return H3(random_bytes || secret_enc)
~~~

## Polynomial Operations {#dep-polynomial}

This section describes operations on and associated with polynomials over Scalars
that are used in the main signing protocol. A polynomial of maximum degree t+1
is represented as a list of t coefficients, where the constant term of the polynomial
is in the first position and the highest-degree coefficient is in the last position.
A point on the polynomial is a tuple (x, y), where `y = f(x)`. For notational
convenience, we refer to the x-coordinate and y-coordinate of a
point p as `p.x` and `p.y`, respectively.

### Evaluation of a polynomial

This section describes a method for evaluating a polynomial `f` at a
particular input `x`, i.e., `y = f(x)` using Horner's method.

~~~
  polynomial_evaluate(x, coeffs):

  Inputs:
  - x, input at which to evaluate the polynomial, a Scalar
  - coeffs, the polynomial coefficients, a list of Scalars

  Outputs: Scalar result of the polynomial evaluated at input x

  def polynomial_evaluate(x, coeffs):
    value = 0
    for coeff in reverse(coeffs):
      value *= x
      value += coeff
    return value
~~~

### Lagrange coefficients

The function `derive_lagrange_coefficient` derives a Lagrange coefficient
to later perform polynomial interpolation, and is provided a list of x-coordinates
as input. Note that `derive_lagrange_coefficient` does not permit any x-coordinate
to equal 0. Lagrange coefficients are used in FROST to evaluate a polynomial `f`
at x-coordinate 0, i.e., `f(0)`, given a list of `t` other x-coordinates.

~~~
  derive_lagrange_coefficient(x_i, L):

  Inputs:
  - x_i, an x-coordinate contained in L, a Scalar
  - L, the set of x-coordinates, each a Scalar

  Outputs: L_i, the i-th Lagrange coefficient

  Errors:
  - "invalid parameters", if 1) any x-coordinate is equal to 0, 2) if x_i
    is not in L, or if 3) any x-coordinate is represented more than once in L.

  def derive_lagrange_coefficient(x_i, L):
    if x_i == 0:
      raise "invalid parameters"
    for x_j in L:
      if x_j == 0:
        raise "invalid parameters"
    if x_i not in L:
      raise "invalid parameters"
    for x_j in L:
      if count(x_i, L) > 1:
        raise "invalid parameters"

    numerator = Scalar(1)
    denominator = Scalar(1)
    for x_j in L:
      if x_j == x_i: continue
      numerator *= x_j
      denominator *= x_j - x_i

    L_i = numerator / denominator
    return L_i
~~~

## List Operations {#dep-encoding}

This section describes helper functions that work on lists of values produced
during the FROST protocol. The following function encodes a list of participant
commitments into a bytestring for use in the FROST protocol.

~~~
  Inputs:
  - commitment_list = [(i, hiding_nonce_commitment_i, binding_nonce_commitment_i), ...],
    a list of commitments issued by each participant, where each element in the list
    indicates the participant identifier i and their two commitment Element values
    (hiding_nonce_commitment_i, binding_nonce_commitment_i). This list MUST be sorted
    in ascending order by participant identifier.

  Outputs: A byte string containing the serialized representation of commitment_list

  def encode_group_commitment_list(commitment_list):
    encoded_group_commitment = nil
    for (identifier, hiding_nonce_commitment, binding_nonce_commitment) in commitment_list:
      encoded_commitment = G.SerializeScalar(identifier) ||
                           G.SerializeElement(hiding_nonce_commitment) ||
                           G.SerializeElement(binding_nonce_commitment)
      encoded_group_commitment = encoded_group_commitment || encoded_commitment
    return encoded_group_commitment
~~~

The following function is used to extract participant identifiers from a commitment
list.

~~~
  Inputs:
  - commitment_list = [(i, hiding_nonce_commitment_i, binding_nonce_commitment_i), ...],
    a list of commitments issued by each participant, where each element in the list
    indicates the participant identifier i and their two commitment Element values
    (hiding_nonce_commitment_i, binding_nonce_commitment_i). This list MUST be sorted
    in ascending order by participant identifier.

  Outputs: A list of participant identifiers

def participants_from_commitment_list(commitment_list):
  identifiers = []
  for (identifier, _, _) in commitment_list:
    identifiers.append(identifier)
  return identifiers
~~~

The following function is used to extract a binding factor from a list of binding factors.

~~~
  Inputs:
  - binding_factor_list = [(i, binding_factor), ...],
    a list of binding factors for each participant, where each element in the list
    indicates the participant identifier i and their binding factor. This list MUST be sorted
    in ascending order by participant identifier.
  - identifier, participant identifier, a Scalar.

  Outputs: A Scalar value.

  Errors: "invalid participant", when the designated participant is not known

def binding_factor_for_participant(binding_factor_list, identifier):
  for (i, binding_factor) in binding_factor_list:
    if identifier == i:
      return binding_factor
  raise "invalid participant"
~~~

## Binding Factors Computation {#dep-binding-factor}

This section describes the subroutine for computing binding factors based
on the participant commitment list and message to be signed.

~~~
  Inputs:
  - commitment_list = [(i, hiding_nonce_commitment_i, binding_nonce_commitment_i), ...],
    a list of commitments issued by each participant, where each element in the list
    indicates the participant identifier i and their two commitment Element values
    (hiding_nonce_commitment_i, binding_nonce_commitment_i). This list MUST be sorted
    in ascending order by participant identifier.
  - msg, the message to be signed.

  Outputs: A list of (identifier, Scalar) tuples representing the binding factors.

  def compute_binding_factors(commitment_list, msg):
    msg_hash = H4(msg)
    encoded_commitment_hash = H5(encode_group_commitment_list(commitment_list))
    rho_input_prefix = msg_hash || encoded_commitment_hash

    binding_factor_list = []
    for (identifier, hiding_nonce_commitment, binding_nonce_commitment) in commitment_list:
      rho_input = rho_input_prefix || G.SerializeScalar(identifier)
      binding_factor = H1(rho_input)
      binding_factor_list.append((identifier, binding_factor))
    return binding_factor_list
~~~

## Group Commitment Computation {#dep-group-commit}

This section describes the subroutine for creating the group commitment
from a commitment list.

~~~
  Inputs:
  - commitment_list =
     [(i, hiding_nonce_commitment_i, binding_nonce_commitment_i), ...], a list
    of commitments issued by each participant, where each element in the list
    indicates the participant identifier i and their two commitment Element values
    (hiding_nonce_commitment_i, binding_nonce_commitment_i). This list MUST be
    sorted in ascending order by participant identifier.
  - binding_factor_list = [(i, binding_factor), ...],
    a list of (identifier, Scalar) tuples representing the binding factor Scalar
    for the given identifier. This list MUST be sorted in ascending order by identifier.

  Outputs: An Element in G representing the group commitment

  def compute_group_commitment(commitment_list, binding_factor_list):
    group_commitment = G.Identity()
    for (identifier, hiding_nonce_commitment, binding_nonce_commitment) in commitment_list:
      binding_factor = binding_factor_for_participant(binding_factors, identifier)
      group_commitment = group_commitment +
        hiding_nonce_commitment + G.ScalarMult(binding_nonce_commitment, binding_factor)
    return group_commitment
~~~

## Signature Challenge Computation {#dep-sig-challenge}

This section describes the subroutine for creating the per-message challenge.

~~~
  Inputs:
  - group_commitment, an Element in G representing the group commitment
  - group_public_key, public key corresponding to the group signing key, an
    Element in G.
  - msg, the message to be signed.

  Outputs: A Scalar representing the challenge

  def compute_challenge(group_commitment, group_public_key, msg):
    group_comm_enc = G.SerializeElement(group_commitment)
    group_public_key_enc = G.SerializeElement(group_public_key)
    challenge_input = group_comm_enc || group_public_key_enc || msg
    challenge = H2(challenge_input)
    return challenge
~~~

# Two-Round FROST Signing Protocol {#frost-spec}

This section describes the two-round variant of the FROST threshold signature
protocol for producing Schnorr signatures. The protocol is configured to
run with a selection of `NUM_PARTICIPANTS` signer participants and a Coordinator.
`NUM_PARTICIPANTS` is a positive integer at least `MIN_PARTICIPANTS` but no larger than
`MAX_PARTICIPANTS`, where `MIN_PARTICIPANTS <= MAX_PARTICIPANTS`, `MIN_PARTICIPANTS` is a positive
integer and `MAX_PARTICIPANTS` is a positive integer less than the group order.
A signer participant, or simply participant, is an entity that is trusted to hold and
use a signing key share. The Coordinator is an entity with the following responsibilities:

1. Determining which participants will participate (at least MIN_PARTICIPANTS in number);
2. Coordinating rounds (receiving and forwarding inputs among participants); and
3. Aggregating signature shares output by each participant, and publishing the resulting signature.

FROST assumes that all parties and their roles, including the Coordinator and the set of participants,
are chosen externally to the protocol. Note that it is possible to deploy the protocol
without a distinguished Coordinator; see {{no-coordinator}} for more information.

FROST produces signatures that are indistinguishable from those produced with a single
participant using a signing key `s` with corresponding public key `PK`, where `s` is a Scalar
value and `PK = G.ScalarMultBase(s)`. As a threshold signing protocol, the group signing
key `s` is secret-shared amongst each participant and used to produce signatures. In particular,
FROST assumes each participant is configured with the following information:

- An identifier, which is a Scalar value denoted `i` in the range `[1, MAX_PARTICIPANTS]`
  and MUST be distinct from the identifier of every other participant.
- A signing key share `sk_i`, which is a Scalar value representing the i-th secret share
  of the group signing key `s`. The public key corresponding to this signing key share
  is `PK_i = G.ScalarMultBase(sk_i)`.

The Coordinator and each participant is additionally configured
with common group information, denoted "group info," which consists of the following
information:

- Group public key, which is an `Element` in `G` denoted `PK`.
- Public keys `PK_i` for each participant, which are `Element` values in `G` denoted `PK_i`
  for each `i` in `[1, MAX_PARTICIPANTS]`.

This document does not specify how this information, including the signing key shares,
are configured and distributed to participants. In general, two possible configuration
mechanisms are possible: one that requires a single, trusted dealer, and the other
which requires performing a distributed key generation protocol. We highlight
key generation mechanism by a trusted dealer in {{dep-dealer}} for reference.

The signing variant of FROST in this document requires participants to perform two network rounds:
1) generating and publishing commitments, and 2) signature share generation and
publication. The first round serves for each participant to issue a commitment to
a nonce. The second round receives commitments for all participants as well as the message,
and issues a signature share with respect to that message. The Coordinator performs
the coordination of each of these rounds. At the end of the second round, the
Coordinator then performs an aggregation step and outputs the final signature.
This complete interaction is shown in {{fig-frost}}.

~~~
        (group info)            (group info,     (group info,
            |               signing key share)   signing key share)
            |                         |                |
            v                         v                v
        Coordinator               Signer-1   ...   Signer-n
    ------------------------------------------------------------
   message
------------>
            |
      == Round 1 (Commitment) ==
            | participant commitment |                 |
            |<-----------------------+                 |
            |          ...                             |
            | participant commitment            (commit state) ==\
            |<-----------------------------------------+         |
                                                                 |
      == Round 2 (Signature Share Generation) ==                 |
            |                                                    |
            |   participant input    |                 |         |
            +------------------------>                 |         |
            |     signature share    |                 |         |
            |<-----------------------+                 |         |
            |          ...                             |         |
            |    participant input                     |         |
            +------------------------------------------>         /
            |     signature share                      |<=======/
            <------------------------------------------+
            |
      == Aggregation ==
            |
  signature |
<-----------+
~~~
{: #fig-frost title="FROST signature overview" }

Details for round one are described in {{frost-round-one}}, and details for round two
are described in {{frost-round-two}}. Note that each participant persists some state between
both rounds, and this state is deleted as described in {{frost-round-two}}. The final
Aggregation step is described in {{frost-aggregation}}.

FROST assumes that all inputs to each round, especially those of which are received
over the network, are validated before use. In particular, this means that any value
of type Element or Scalar is deserialized using DeserializePrimeOrderElement and DeserializeScalar,
respectively, as these functions perform the necessary input validation steps.

FROST assumes reliable message delivery between the Coordinator and participants in
order for the protocol to complete. An attacker masquerading as another participant
will result only in an invalid signature; see {{sec-considerations}}. However, in order
to identify any participant which has misbehaved (resulting in the protocol aborting)
to take actions such as excluding them from future signing operations, we assume that
the network channel is additionally authenticated; confidentiality is not required.

## Round One - Commitment {#frost-round-one}

Round one involves each participant generating nonces and their corresponding public commitments.
A nonce is a pair of Scalar values, and a commitment is a pair of Element values. Each participant's
behavior in this round is described by the `commit` function below. Note that this function
invokes `nonce_generate` twice, once for each type of nonce produced. The output of this function is
a pair of secret nonces `(hiding_nonce, binding_nonce)` and their corresponding public commitments
`(hiding_nonce_commitment, binding_nonce_commitment)`.

~~~
  Inputs: sk_i, the secret key share, a Scalar

  Outputs: (nonce, comm), a tuple of nonce and nonce commitment pairs,
    where each value in the nonce pair is a Scalar and each value in
    the nonce commitment pair is an Element

  def commit(sk_i):
    hiding_nonce = nonce_generate(sk_i)
    binding_nonce = nonce_generate(sk_i)
    hiding_nonce_commitment = G.ScalarBaseMult(hiding_nonce)
    binding_nonce_commitment = G.ScalarBaseMult(binding_nonce)
    nonce = (hiding_nonce, binding_nonce)
    comm = (hiding_nonce_commitment, binding_nonce_commitment)
    return (nonce, comm)
~~~

The outputs `nonce` and `comm` from participant `P_i` should both be stored locally and
kept for use in the second round. The `nonce` value is secret and MUST NOT be shared, whereas
the public output `comm` is sent to the Coordinator, serializing group Elements using
`SerializePrimeOrderElement` from {{dep-pog}}. The nonce values produced by this function MUST NOT
be reused in more than one invocation of FROST, and it MUST be generated from a source of secure
randomness.

<!-- The Coordinator must not get confused about which commitments come from which signers, do we need to say more about how this is done? -->

## Round Two - Signature Share Generation {#frost-round-two}

In round two, the Coordinator is responsible for sending the message to be signed, and
for choosing which participants will participate (of number at least MIN_PARTICIPANTS). Signers
additionally require locally held data; specifically, their private key and the
nonces corresponding to their commitment issued in round one.

The Coordinator begins by sending each participant the message to be signed along with the
set of signing commitments for all participants in the participant list, serializing each group
Element using SerializePrimeOrderElement from {{dep-pog}}. Each participant MUST validate the inputs
before processing the Coordinator's request. In particular, the Signer MUST validate commitment_list,
deserializing each group Element in the list using DeserializePrimeOrderElement from {{dep-pog}}.
If deserialization fails, the Signer MUST abort the protocol. Moreover, each participant MUST ensure
that their identifier as well as their commitment as from the first round appears in commitment_list.
Applications which require that participants not process arbitrary
input messages are also required to also perform relevant application-layer input
validation checks; see {{message-validation}} for more details.

Upon receipt and successful input validation, each Signer then runs the following
procedure to produce its own signature share.

~~~
  Inputs:
  - identifier, Identifier i of the participant. Note identifier will never equal 0.
  - sk_i, Signer secret key share, a Scalar.
  - group_public_key, public key corresponding to the group signing key,
    an Element in G.
  - nonce_i, pair of Scalar values (hiding_nonce, binding_nonce) generated in
    round one.
  - msg, the message to be signed (sent by the Coordinator).
  - commitment_list =
      [(j, hiding_nonce_commitment_j, binding_nonce_commitment_j), ...], a
    list of commitments issued in Round 1 by each participant and sent by the Coordinator.
    Each element in the list indicates the participant identifier j and their two commitment
    Element values (hiding_nonce_commitment_j, binding_nonce_commitment_j).
    This list MUST be sorted in ascending order by participant identifier.

  Outputs: a Scalar value representing the signature share

  def sign(identifier, sk_i, group_public_key, nonce_i, msg, commitment_list):
    # Compute the binding factor(s)
    binding_factor_list = compute_binding_factors(commitment_list, msg)
    binding_factor = binding_factor_for_participant(binding_factor_list, identifier)

    # Compute the group commitment
    group_commitment = compute_group_commitment(commitment_list, binding_factor_list)

    # Compute Lagrange coefficient
    participant_list = participants_from_commitment_list(commitment_list)
    lambda_i = derive_lagrange_coefficient(identifier, participant_list)

    # Compute the per-message challenge
    challenge = compute_challenge(group_commitment, group_public_key, msg)

    # Compute the signature share
    (hiding_nonce, binding_nonce) = nonce_i
    sig_share = hiding_nonce + (binding_nonce * binding_factor) + (lambda_i * sk_i * challenge)

    return sig_share
~~~

The output of this procedure is a signature share. Each participant then sends
these shares back to the Coordinator. Each participant MUST delete the nonce and
corresponding commitment after this round completes, and MUST use the nonce
to generate at most one signature share.

Note that the `lambda_i` value derived during this procedure does not change
across FROST signing operations for the same signing group. As such, participants
can compute it once and store it for reuse across signing sessions.

Upon receipt from each Signer, the Coordinator MUST validate the input
signature share using DeserializePrimeOrderElement. If validation fails, the Coordinator MUST abort
the protocol. If validation succeeds, the Coordinator then verifies the set of
signature shares using the following procedure.

## Signature Share Verification and Aggregation {#frost-aggregation}

After participants perform round two and send their signature shares to the Coordinator,
the Coordinator verifies each signature share for correctness. In particular,
for each participant, the Coordinator uses commitment pairs generated during round
one and the signature share generated during round two, along with other group
parameters, to check that the signature share is valid using the following procedure.

~~~
  Inputs:
  - identifier, Identifier i of the participant. Note: identifier MUST never equal 0.
  - PK_i, the public key for the ith participant, where PK_i = G.ScalarBaseMult(sk_i),
    an Element in G
  - comm_i, pair of Element values in G (hiding_nonce_commitment, binding_nonce_commitment)
    generated in round one from the ith participant.
  - sig_share_i, a Scalar value indicating the signature share as produced in
    round two from the ith participant.
  - commitment_list =
      [(j, hiding_nonce_commitment_j, binding_nonce_commitment_j), ...], a
    list of commitments issued in Round 1 by each participant, where each element
    in the list indicates the participant identifier j and their two commitment
    Element values (hiding_nonce_commitment_j, binding_nonce_commitment_j).
    This list MUST be sorted in ascending order by participant identifier.
  - group_public_key, public key corresponding to the group signing key,
    an Element in G.
  - msg, the message to be signed.

  Outputs: True if the signature share is valid, and False otherwise.

  def verify_signature_share(identifier, PK_i, comm_i, sig_share_i, commitment_list,
                             group_public_key, msg):
    # Compute the binding factors
    binding_factor_list = compute_binding_factors(commitment_list, msg)
    binding_factor = binding_factor_for_participant(binding_factor_list, identifier)

    # Compute the group commitment
    group_commitment = compute_group_commitment(commitment_list, binding_factor_list)

    # Compute the commitment share
    (hiding_nonce_commitment, binding_nonce_commitment) = comm_i
    comm_share = hiding_nonce_commitment + G.ScalarMult(binding_nonce_commitment, binding_factor)

    # Compute the challenge
    challenge = compute_challenge(group_commitment, group_public_key, msg)

    # Compute Lagrange coefficient
    participant_list = participants_from_commitment_list(commitment_list)
    lambda_i = derive_lagrange_coefficient(identifier, participant_list)

    # Compute relation values
    l = G.ScalarBaseMult(sig_share_i)
    r = comm_share + G.ScalarMult(PK_i, challenge * lambda_i)

    return l == r
~~~

If any signature share fails to verify, i.e., if verify_signature_share returns False for
any participant share, the Coordinator MUST abort the protocol for correctness reasons
(this is true regardless of the size or makeup of the signing set selected by
the Coordinator).
Excluding one participant means that their nonce will not be included in the joint response `z`
and consequently the output signature will not verify. This is because the
group commitment will be with respect to a different signing set than the
the aggregated response.

Otherwise, if all shares from participants that participated in Rounds 1 and 2 are valid, the Coordinator
performs the `aggregate` operation and publishes the resulting signature.

~~~
  Inputs:
  - group_commitment, the group commitment returned by compute_group_commitment,
    an Element in G.
  - sig_shares, a set of signature shares z_i, Scalar values, for each participant,
    of length NUM_PARTICIPANTS, where MIN_PARTICIPANTS <= NUM_PARTICIPANTS <= MAX_PARTICIPANTS.

  Outputs: (R, z), a Schnorr signature consisting of an Element R and Scalar z.

  def aggregate(group_commitment, sig_shares):
    z = 0
    for z_i in sig_shares:
      z = z + z_i
    return (group_commitment, z)
~~~

The output signature (R, z) from the aggregation step MUST be encoded as follows
(using notation from {{Section 3 of TLS}}):

~~~
  struct {
    opaque R_encoded[Ne];
    opaque z_encoded[Ns];
  } Signature;
~~~

Where Signature.R_encoded is `G.SerializeElement(R)` and Signature.z_encoded is
`G.SerializeScalar(z)`.

# Ciphersuites {#ciphersuites}

A FROST ciphersuite must specify the underlying prime-order group details
and cryptographic hash function. Each ciphersuite is denoted as (Group, Hash),
e.g., (ristretto255, SHA-512). This section contains some ciphersuites.
Each ciphersuite also includes a context string, denoted `contextString`,
which is an ASCII string literal (with no NULL terminating character).

The RECOMMENDED ciphersuite is (ristretto255, SHA-512) {{recommended-suite}}.
The (Ed25519, SHA-512) ciphersuite is included for backwards compatibility
with {{!RFC8032}}.

The DeserializeElement and DeserializeScalar functions instantiated for a
particular group corresponding to a ciphersuite MUST adhere
to the description in {{dep-pog}}. Validation steps for these functions
are described for each the ciphersuites below. Future ciphersuites MUST
describe how input validation is done for DeserializeElement and DeserializeScalar.

Signatures produced by a ciphersuite must be verifiable as specified in {{prime-order-verify}}.
Note that these instructions are equivalent to those produced by a single participant.

## FROST(Ed25519, SHA-512)

This ciphersuite uses edwards25519 for the Group and SHA-512 for the Hash function `H`
meant to produce signatures indistinguishable from Ed25519 as specified in {{!RFC8032}}.
The value of the contextString parameter is "FROST-ED25519-SHA512-v10".

- Group: edwards25519 {{!RFC8032}}
  - Cofactor(): Return 8.
  - Order(): Return 2^252 + 27742317777372353535851937790883648493 (see {{?RFC7748}})
  - Identity(): As defined in {{RFC7748}}.
  - RandomScalar(): Implemented by returning a uniformly random Scalar in the range
    \[0, `G.Order()` - 1\]. Refer to {{random-scalar}} for implementation guidance.
  - SerializeElement(A): Implemented as specified in {{!RFC8032, Section 5.1.2}}.
  - DeserializeElement(buf): Implemented as specified in {{!RFC8032, Section 5.1.3}}.
    Additionally, this function validates that the resulting element is not the group
    identity element.
  - SerializeScalar(s): Implemented by outputting the little-endian 32-byte encoding of
    the Scalar value with the top three bits set to zero.
  - DeserializeScalar(buf): Implemented by attempting to deserialize a Scalar from a
    little-endian 32-byte string. This function can fail if the input does not
    represent a Scalar in the range \[0, `G.Order()` - 1\]. Note that this means the
    top three bits of the input MUST be zero.

- Hash (`H`): SHA-512
  - H1(m): Implemented by computing H(contextString \|\| "rho" \|\| m), interpreting the 64-byte digest
    as a little-endian integer, and reducing the resulting integer modulo
    2^252+27742317777372353535851937790883648493.
  - H2(m): Implemented by computing H(m), interpreting the 64-byte digest
    as a little-endian integer, and reducing the resulting integer modulo
    2^252+27742317777372353535851937790883648493.
  - H3(m): Implemented by computing H(contextString \|\| "nonce" \|\| m), interpreting the 64-byte digest
    as a little-endian integer, and reducing the resulting integer modulo
    2^252+27742317777372353535851937790883648493.
  - H4(m): Implemented by computing H(contextString \|\| "msg" \|\| m).
  - H5(m): Implemented by computing H(contextString \|\| "com" \|\| m).

Normally H2 would also include a domain separator, but for backwards compatibility
with {{!RFC8032}}, it is omitted.

## FROST(ristretto255, SHA-512) {#recommended-suite}

This ciphersuite uses ristretto255 for the Group and SHA-512 for the Hash function `H`.
The value of the contextString parameter is "FROST-RISTRETTO255-SHA512-v10".

- Group: ristretto255 {{!RISTRETTO=I-D.irtf-cfrg-ristretto255-decaf448}}
  - Cofactor(): Return 1.
  - Order(): Return 2^252 + 27742317777372353535851937790883648493 (see {{RISTRETTO}})
  - Identity(): As defined in {{RISTRETTO}}.
  - RandomScalar(): Implemented by returning a uniformly random Scalar in the range
    \[0, `G.Order()` - 1\]. Refer to {{random-scalar}} for implementation guidance.
  - SerializeElement(A): Implemented using the 'Encode' function from {{!RISTRETTO}}.
  - DeserializeElement(buf): Implemented using the 'Decode' function from {{!RISTRETTO}}.
    Additionally, this function validates that the resulting element is not the group
    identity element.
  - SerializeScalar(s): Implemented by outputting the little-endian 32-byte encoding of
    the Scalar value with the top three bits set to zero.
  - DeserializeScalar(buf): Implemented by attempting to deserialize a Scalar from a
    little-endian 32-byte string. This function can fail if the input does not
    represent a Scalar in the range \[0, `G.Order()` - 1\]. Note that this means the
    top three bits of the input MUST be zero.

- Hash (`H`): SHA-512
  - H1(m): Implemented by computing H(contextString || "rho" || m) and mapping the
    output to a Scalar as described in {{!RISTRETTO, Section 4.4}}.
  - H2(m): Implemented by computing H(contextString || "chal" || m) and mapping the
    output to a Scalar as described in {{!RISTRETTO, Section 4.4}}.
  - H3(m): Implemented by computing H(contextString \|\| "nonce" \|\| m) and mapping the
    output to a Scalar as described in {{!RISTRETTO, Section 4.4}}.
  - H4(m): Implemented by computing H(contextString \|\| "msg" \|\| m).
  - H5(m): Implemented by computing H(contextString \|\| "com" \|\| m).

## FROST(Ed448, SHAKE256)

This ciphersuite uses edwards448 for the Group and SHAKE256 for the Hash function `H`
meant to produce signatures indistinguishable from Ed448 as specified in {{!RFC8032}}.
The value of the contextString parameter is "FROST-ED448-SHAKE256-v10".

- Group: edwards448 {{!RFC8032}}
  - Cofactor(): Return 4.
  - Order(): Return 2^446 - 13818066809895115352007386748515426880336692474882178609894547503885
  - Identity(): As defined in {{RFC7748}}.
  - RandomScalar(): Implemented by returning a uniformly random Scalar in the range
    \[0, `G.Order()` - 1\]. Refer to {{random-scalar}} for implementation guidance.
  - SerializeElement(A): Implemented as specified in {{!RFC8032, Section 5.2.2}}.
  - DeserializeElement(buf): Implemented as specified in {{!RFC8032, Section 5.2.3}}.
    Additionally, this function validates that the resulting element is not the group
    identity element.
  - SerializeScalar(s): Implemented by outputting the little-endian 48-byte encoding of
    the Scalar value.
  - DeserializeScalar(buf): Implemented by attempting to deserialize a Scalar from a
    little-endian 48-byte string. This function can fail if the input does not
    represent a Scalar in the range \[0, `G.Order()` - 1\].

- Hash (`H`): SHAKE256
  - H1(m): Implemented by computing H(contextString \|\| "rho" \|\| m), interpreting the
    114-byte digest as a little-endian integer, and reducing the resulting integer modulo
    2^446 - 13818066809895115352007386748515426880336692474882178609894547503885.
  - H2(m): Implemented by computing H("SigEd448" \|\| 0 \|\| 0 \|\| m), interpreting
    the 114-byte digest as a little-endian integer, and reducing the resulting integer
    modulo 2^446 - 13818066809895115352007386748515426880336692474882178609894547503885.
  - H3(m): Implemented by computing H(contextString \|\| "nonce" \|\| m), interpreting the
    114-byte digest as a little-endian integer, and reducing the resulting integer modulo
    2^446 - 13818066809895115352007386748515426880336692474882178609894547503885.
  - H4(m): Implemented by computing H(contextString \|\| "msg" \|\| m).
  - H5(m): Implemented by computing H(contextString \|\| "com" \|\| m).

Normally H2 would also include a domain separator, but for backwards compatibility
with {{!RFC8032}}, it is omitted.

## FROST(P-256, SHA-256)

This ciphersuite uses P-256 for the Group and SHA-256 for the Hash function `H`.
The value of the contextString parameter is "FROST-P256-SHA256-v10".

- Group: P-256 (secp256r1) {{x9.62}}
  - Cofactor(): Return 1.
  - Order(): Return 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
  - Identity(): As defined in {{x9.62}}.
  - RandomScalar(): Implemented by returning a uniformly random Scalar in the range
    \[0, `G.Order()` - 1\]. Refer to {{random-scalar}} for implementation guidance.
  - SerializeElement(A): Implemented using the compressed Elliptic-Curve-Point-to-Octet-String
    method according to {{SEC1}}, yielding a 33 byte output.
  - DeserializeElement(buf): Implemented by attempting to deserialize a 33 byte input string to
    a public key using the compressed Octet-String-to-Elliptic-Curve-Point method according to {{SEC1}},
    and then performs partial public-key validation as defined in section 5.6.2.3.4 of
    {{!KEYAGREEMENT=DOI.10.6028/NIST.SP.800-56Ar3}}. This includes checking that the
    coordinates of the resulting point are in the correct range, that the point is on
    the curve, and that the point is not the point at infinity. Additionally, this function
    validates that the resulting element is not the group identity element.
    If these checks fail, deserialization returns an error.
  - SerializeScalar(s): Implemented using the Field-Element-to-Octet-String conversion
    according to {{SEC1}}.
  - DeserializeScalar(buf): Implemented by attempting to deserialize a Scalar from a 32-byte
    string using Octet-String-to-Field-Element from {{SEC1}}. This function can fail if the
    input does not represent a Scalar in the range \[0, `G.Order()` - 1\].

- Hash (`H`): SHA-256
  - H1(m): Implemented as hash_to_field(m, 1) from {{!HASH-TO-CURVE=I-D.irtf-cfrg-hash-to-curve, Section 5.2}}
    using `expand_message_xmd` with SHA-256 with parameters DST = contextString || "rho",
    F set to the scalar field, p set to `G.Order()`, m = 1, and L = 48.
  - H2(m): Implemented as hash_to_field(m, 1) from {{!HASH-TO-CURVE, Section 5.2}}
    using `expand_message_xmd` with SHA-256 with parameters DST = contextString || "chal",
    F set to the scalar field, p set to `G.Order()`, m = 1, and L = 48.
  - H3(m): Implemented as hash_to_field(m, 1) from {{!HASH-TO-CURVE, Section 5.2}}
    using `expand_message_xmd` with SHA-256 with parameters DST = contextString || "nonce",
    F set to the scalar field, p set to `G.Order()`, m = 1, and L = 48.
  - H4(m): Implemented by computing H(contextString \|\| "msg" \|\| m).
  - H5(m): Implemented by computing H(contextString \|\| "com" \|\| m).

## FROST(secp256k1, SHA-256)

This ciphersuite uses secp256k1 for the Group and SHA-256 for the Hash function `H`.
The value of the contextString parameter is "FROST-secp256k1-SHA256-v10".

- Group: secp256k1 {{SEC2}}
  - Cofactor(): Return 1.
  - Order(): Return 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
  - Identity(): As defined in {{SEC2}}.
  - RandomScalar(): Implemented by returning a uniformly random Scalar in the range
    \[0, `G.Order()` - 1\]. Refer to {{random-scalar}} for implementation guidance.
  - SerializeElement(A): Implemented using the compressed Elliptic-Curve-Point-to-Octet-String
    method according to {{SEC1}}.
  - DeserializeElement(buf): Implemented by attempting to deserialize a public key using
    the compressed Octet-String-to-Elliptic-Curve-Point method according to {{SEC1}},
    and then performs partial public-key validation as defined in section 3.2.2.1 of
    {{SEC1}}. This includes checking that the coordinates of the resulting point are
    in the correct range, that the point is on the curve, and that the point is not
    the point at infinity. Additionally, this function validates that the resulting
    element is not the group identity element. If these checks fail, deserialization
    returns an error.
  - SerializeScalar(s): Implemented using the Field-Element-to-Octet-String conversion
    according to {{SEC1}}.
  - DeserializeScalar(buf): Implemented by attempting to deserialize a Scalar from a 32-byte
    string using Octet-String-to-Field-Element from {{SEC1}}. This function can fail if the
    input does not represent a Scalar in the range \[0, `G.Order()` - 1\].

- Hash (`H`): SHA-256
  - H1(m): Implemented as hash_to_field(m, 1) from {{!HASH-TO-CURVE=I-D.irtf-cfrg-hash-to-curve, Section 5.2}}
    using `expand_message_xmd` with SHA-256 with parameters DST = contextString || "rho",
    F set to the scalar field, p set to `G.Order()`, m = 1, and L = 48.
  - H2(m): Implemented as hash_to_field(m, 1) from {{!HASH-TO-CURVE, Section 5.2}}
    using `expand_message_xmd` with SHA-256 with parameters DST = contextString || "chal",
    F set to the scalar field, p set to `G.Order()`, m = 1, and L = 48.
  - H3(m): Implemented as hash_to_field(m, 1) from {{!HASH-TO-CURVE, Section 5.2}}
    using `expand_message_xmd` with SHA-256 with parameters DST = contextString || "nonce",
    F set to the scalar field, p set to `G.Order()`, m = 1, and L = 48.
  - H4(m): Implemented by computing H(contextString \|\| "msg" \|\| m).
  - H5(m): Implemented by computing H(contextString \|\| "com" \|\| m).

# Security Considerations {#sec-considerations}

A security analysis of FROST exists in {{FROST20}} and {{Schnorr21}}. The protocol as specified
in this document assumes the following threat model.

* Trusted dealer. The dealer that performs key generation is trusted to follow
the protocol, although participants still are able to verify the consistency of their
shares via a VSS (verifiable secret sharing) step; see {{dep-vss}}.

* Unforgeability assuming at most `(MIN_PARTICIPANTS-1)` corrupted participants. So long as an adversary
corrupts fewer than `MIN_PARTICIPANTS` participants, the scheme remains secure against Existential
Unforgeability Under Chosen Message Attack (EUF-CMA) attacks, as defined in {{BonehShoup}},
Definition 13.2.

* Coordinator. We assume the Coordinator at the time of signing does not perform a
denial of service attack. A denial of service would include any action which either
prevents the protocol from completing or causing the resulting signature to be invalid.
Such actions for the latter include sending inconsistent values to participants,
such as messages or the set of individual commitments. Note that the Coordinator
is *not* trusted with any private information and communication at the time of signing
can be performed over a public but reliable channel.

The protocol as specified in this document does not target the following goals:

* Post quantum security. FROST, like plain Schnorr signatures, requires the hardness of the Discrete Logarithm Problem.
* Robustness. In the case of failure, FROST requires aborting the protocol.
* Downgrade prevention. All participants in the protocol are assumed to agree on what algorithms to use.
* Metadata protection. If protection for metadata is desired, a higher-level communication
channel can be used to facilitate key generation and signing.

The rest of this section documents issues particular to implementations or deployments.

## Nonce Reuse Attacks

{{dep-nonces}} describes the procedure that participants use to produce nonces during
the first round of singing. The randomness produced in this procedure MUST be sampled
uniformly at random. The resulting nonces produced via `nonce_generate` are indistinguishable
from values sampled uniformly at random. This requirement is necessary to avoid
replay attacks initiated by other participants, which allow for a complete key-recovery attack.
The Coordinator MAY further hedge against nonce reuse attacks by tracking participant nonce
commitments used for a given group key, at the cost of additional state.

## Protocol Failures

We do not specify what implementations should do when the protocol fails, other than requiring that
the protocol abort. Examples of viable failure include when a verification check returns invalid or
if the underlying transport failed to deliver the required messages.

## Removing the Coordinator Role {#no-coordinator}

In some settings, it may be desirable to omit the role of the Coordinator entirely.
Doing so does not change the security implications of FROST, but instead simply
requires each participant to communicate with all other participants. We loosely
describe how to perform FROST signing among participants without this coordinator role.
We assume that every participant receives as input from an external source the
message to be signed prior to performing the protocol.

Every participant begins by performing `commit()` as is done in the setting
where a Coordinator is used. However, instead of sending the commitment
to the Coordinator, every participant instead will publish
this commitment to every other participant. Then, in the second round, participants will already have
sufficient information to perform signing. They will directly perform `sign()`.
All participants will then publish their signature shares to one another. After having
received all signature shares from all other participants, each participant will then perform
`verify_signature_share` and then `aggregate` directly.

The requirements for the underlying network channel remain the same in the setting
where all participants play the role of the Coordinator, in that all messages that
are exchanged are public and so the channel simply must be reliable. However, in
the setting that a player attempts to split the view of all other players by
sending disjoint values to a subset of players, the signing operation will output
an invalid signature. To avoid this denial of service, implementations may wish
to define a mechanism where messages are authenticated, so that cheating players
can be identified and excluded.

## Input Message Hashing {#pre-hashing}

FROST signatures do not pre-hash message inputs. This means that the entire message
must be known in advance of invoking the signing protocol. Applications can apply
pre-hashing in settings where storing the full message is prohibitively expensive.
In such cases, pre-hashing MUST use a collision-resistant hash function with a security
level commensurate with the security in inherent to the ciphersuite chosen. It is
RECOMMENDED that applications which choose to apply pre-hashing use the hash function
(`H`) associated with the chosen ciphersuite in a manner similar to how `H4` is defined.
In particular, a different prefix SHOULD be used to differentiate this pre-hash from
`H4`. One possible example is to construct this pre-hash over message `m` as
`H(contextString \|\| "pre-hash" \|\| m)`.

## Input Message Validation {#message-validation}

Some applications may require that participants only process messages of a certain
structure. For example, in digital currency applications wherein multiple
participants may collectively sign a transaction, it is reasonable to require that
each participant check the input message to be a syntactically valid transaction.

As another example, use of threshold signatures in {{?TLS=RFC8446}} to produce
signatures of transcript hashes might require the participants receive the source
handshake messages themselves, and recompute the transcript hash which is used
as input message to the signature generation process, so that they can verify
that they are signing a proper TLS transcript hash and not some other data.

In general, input message validation is an application-specific consideration
that varies based on the use case and threat model. However, it is RECOMMENDED
that applications take additional precautions and validate inputs so that participants
do not operate as signing oracles for arbitrary messages.

# Contributors


--- back

# Acknowledgments

This document was improved based on input and contributions by the Zcash Foundation engineering team.
In addition, the authors of this document would like to thank
Isis Lovecruft,
Alden Torres,
T. Wilson-Brown,
and Conrado Gouvea
for their inputs and contributions.

# Schnorr Signature Generation and Verification for Prime-Order Groups {#prime-order-verify}

This section contains descriptions of functions for generating and verifying Schnorr signatures
containing prime-order values. It is included to complement the routines present in {{RFC8032}}.
The functions for generating and verifying signatures are `prime_order_sign` and `prime_order_verify`,
respectively.

The function `prime_order_sign` produces a Schnorr signature over a message given a full secret signing
key as input (as opposed to a key share.)

~~~
  prime_order_sign(msg, sk):
``

  Inputs:
  - msg, message to sign, a byte string
  - sk, secret key, a Scalar

  Outputs: (R, z), a Schnorr signature consisting of an Element R and Scalar z.

  def prime_order_sign(msg, sk):
    r = G.RandomScalar()
    R = G.ScalarBaseMult(r)
    PK = G.ScalarBaseMult(sk)
    comm_enc = G.SerializeElement(R)
    pk_enc = G.SerializeElement(PK)
    challenge_input = comm_enc || pk_enc || msg
    c = H2(challenge_input)
    z = r + (c * sk) // Scalar addition and multiplication
    return (R, z)
~~~

The function `prime_order_verify` verifies Schnorr signatures with validated inputs.
Specifically, it assumes that signature R component and public key belong to the prime-order group.

~~~
  prime_order_verify(msg, sig, PK):

  Inputs:
  - msg, signed message, a byte string
  - sig, a tuple (R, z) output from signature generation
  - PK, public key, an Element

  Outputs: 1 if signature is valid, and 0 otherwise

  def prime_order_verify(msg, sig = (R, z), PK):
    comm_enc = G.SerializeElement(R)
    pk_enc = G.SerializeElement(PK)
    challenge_input = comm_enc || pk_enc || msg
    c = H2(challenge_input)

    l = G.ScalarBaseMult(z)
    r = R + G.ScalarMult(PK, c)
    return l == r
~~~

# Trusted Dealer Key Generation {#dep-dealer}

One possible key generation mechanism is to depend on a trusted dealer, wherein the
dealer generates a group secret `s` uniformly at random and uses Shamir and Verifiable
Secret Sharing as described in {{dep-shamir}} and {{dep-vss}} to create secret
shares of s, denoted `s_i` for `i = 0, ..., MAX_PARTICIPANTS`, to be sent to all `MAX_PARTICIPANTS` participants.
This operation is specified in the `trusted_dealer_keygen` algorithm. The mathematical relation
between the secret key `s` and the `MAX_SIGNER` secret shares is formalized in the `secret_share_combine(shares)`
algorithm, defined in {{dep-shamir}}.

The dealer that performs `trusted_dealer_keygen` is trusted to 1) generate good randomness, and 2) delete secret values after distributing shares to each participant, and 3) keep secret values confidential.

~~~
  Inputs:
  - secret_key, a group secret, a Scalar, that MUST be derived from at least Ns bytes of entropy
  - MAX_PARTICIPANTS, the number of shares to generate, an integer
  - MIN_PARTICIPANTS, the threshold of the secret sharing scheme, an integer

  Outputs:
  - participant_private_keys, MAX_PARTICIPANTS shares of the secret key s, each a tuple
    consisting of the participant identifier and the key share (a Scalar).
  - group_public_key, public key corresponding to the group signing key, an
    Element in G.
  - vss_commitment, a vector commitment of Elements in G, to each of the coefficients
    in the polynomial defined by secret_key_shares and whose first element is
    G.ScalarBaseMult(s).

  def trusted_dealer_keygen(secret_key, MAX_PARTICIPANTS, MIN_PARTICIPANTS):
    # Generate random coefficients for the polynomial
    coefficients = []
    for i in range(0, MIN_PARTICIPANTS - 1):
      coefficients.append(G.RandomScalar())
    participant_private_keys, coefficients = secret_share_shard(secret_key, coefficients, MAX_PARTICIPANTS, MIN_PARTICIPANTS)
    vss_commitment = vss_commit(coefficients):
    return participant_private_keys, vss_commitment[0], vss_commitment
~~~

It is assumed the dealer then sends one secret key share to each of the `NUM_PARTICIPANTS` participants, along with `vss_commitment`.
After receiving their secret key share and `vss_commitment`, participants MUST abort if they do not have the same view of `vss_commitment`.
Otherwise, each participant MUST perform `vss_verify(secret_key_share_i, vss_commitment)`, and abort if the check fails.
The trusted dealer MUST delete the secret_key and secret_key_shares upon completion.

Use of this method for key generation requires a mutually authenticated secure channel
between the dealer and participants to send secret key shares, wherein the channel provides confidentiality
and integrity. Mutually authenticated TLS is one possible deployment option.

## Shamir Secret Sharing {#dep-shamir}

In Shamir secret sharing, a dealer distributes a secret `Scalar` `s` to `n` participants
in such a way that any cooperating subset of `MIN_PARTICIPANTS` participants can recover the
secret. There are two basic steps in this scheme: (1) splitting a secret into
multiple shares, and (2) combining shares to reveal the resulting secret.

This secret sharing scheme works over any field `F`. In this specification, `F` is
the scalar field of the prime-order group `G`.

The procedure for splitting a secret into shares is as follows.

~~~
  secret_share_shard(s, coefficients, MAX_PARTICIPANTS, MIN_PARTICIPANTS):

  Inputs:
  - s, secret value to be shared, a Scalar
  - coefficients, an array of size MIN_PARTICIPANTS - 1 with randomly generated
    Scalars, not including the 0th coefficient of the polynomial
  - MAX_PARTICIPANTS, the number of shares to generate, an integer less than 2^16
  - MIN_PARTICIPANTS, the threshold of the secret sharing scheme, an integer greater than 0

  Outputs:
  - secret_key_shares, A list of MAX_PARTICIPANTS number of secret shares, each a tuple
    consisting of the participant identifier and the key share (a Scalar)
  - coefficients, a vector of MIN_PARTICIPANTS coefficients which uniquely determine a polynomial f.

  Errors:
  - "invalid parameters", if MIN_PARTICIPANTS > MAX_PARTICIPANTS or if MIN_PARTICIPANTS is less than 2

  def secret_share_shard(s, coefficients, MAX_PARTICIPANTS, MIN_PARTICIPANTS):
    if MIN_PARTICIPANTS > MAX_PARTICIPANTS:
      raise "invalid parameters"
    if MIN_PARTICIPANTS < 2:
      raise "invalid parameters"

    # Prepend the secret to the coefficients
    coefficients = [s] + coefficients

    # Evaluate the polynomial for each point x=1,...,n
    secret_key_shares = []
    for x_i in range(1, MAX_PARTICIPANTS + 1):
      y_i = polynomial_evaluate(Scalar(x_i), coefficients)
      secret_key_share_i = (x_i, y_i)
      secret_key_share.append(secret_key_share_i)
    return secret_key_shares, coefficients
~~~

Let `points` be the output of this function. The i-th element in `points` is
the share for the i-th participant, which is the randomly generated polynomial
evaluated at coordinate `i`. We denote a secret share as the tuple `(i, points[i])`,
and the list of these shares as `shares`.
`i` MUST never equal `0`; recall that `f(0) = s`, where `f` is the polynomial defined in a Shamir secret sharing operation.

The procedure for combining a `shares` list of length `MIN_PARTICIPANTS` to recover the
secret `s` is as follows; the algorithm `polynomial_interpolation is defined in {{dep-polynomial-interpolate}}`.

~~~
  secret_share_combine(shares):

  Inputs:
  - shares, a list of at minimum MIN_PARTICIPANTS secret shares, each a tuple (i, f(i))
    where i and f(i) are Scalars

  Outputs: The resulting secret s, a Scalar, that was previously split into shares

  Errors:
  - "invalid parameters", if fewer than MIN_PARTICIPANTS input shares are provided

  def secret_share_combine(shares):
    if len(shares) < MIN_PARTICIPANTS:
      raise "invalid parameters"
    s = polynomial_interpolation(shares)
    return s
~~~

### Deriving the constant term of a polynomial  {#dep-polynomial-interpolate}

Secret sharing requires "splitting" a secret, which is represented as
a constant term of some polynomial `f` of degree `t-1`. Recovering the
constant term occurs with a set of `t` points using polynomial
interpolation, defined as follows.

~~~
  Inputs:
  - points, a set of t distinct points on a polynomial f, each a tuple of two
    Scalar values representing the x and y coordinates

  Outputs: The constant term of f, i.e., f(0)

  def polynomial_interpolation(points):
    x_coords = []
    for point in points:
      x_coords.append(point.x)

    f_zero = Scalar(0)
    for point in points:
      delta = point.y * derive_lagrange_coefficient(point.x, x_coords)
      f_zero = f_zero + delta

    return f_zero
~~~

## Verifiable Secret Sharing {#dep-vss}

Feldman's Verifiable Secret Sharing (VSS) builds upon Shamir secret sharing,
adding a verification step to demonstrate the consistency of a participant's
share with a public commitment to the polynomial `f` for which the secret `s`
is the constant term. This check ensures that all participants have a point
(their share) on the same polynomial, ensuring that they can later reconstruct
the correct secret.

The procedure for committing to a polynomial `f` of degree at most `MIN_PARTICIPANTS-1` is as follows.

~~~
  vss_commit(coeffs):

  Inputs:
  - coeffs, a vector of the MIN_PARTICIPANTS coefficients which uniquely determine
  a polynomial f.

  Outputs: a commitment vss_commitment, which is a vector commitment to each of the
  coefficients in coeffs, where each element of the vector commitment is an Element in G.

  def vss_commit(coeffs):
    vss_commitment = []
    for coeff in coeffs:
      A_i = G.ScalarBaseMult(coeff)
      vss_commitment.append(A_i)
    return vss_commitment
~~~

The procedure for verification of a participant's share is as follows.
If `vss_verify` fails, the participant MUST abort the protocol, and failure should be investigated out of band.

~~~
  vss_verify(share_i, vss_commitment):

  Inputs:
  - share_i: A tuple of the form (i, sk_i), where i indicates the participant
    identifier, and sk_i the participant's secret key, a secret share of the
    constant term of f, where sk_i is a Scalar.
  - vss_commitment: A VSS commitment to a secret polynomial f, a vector commitment
    to each of the coefficients in coeffs, where each element of the vector commitment
    is an Element

  Outputs: 1 if sk_i is valid, and 0 otherwise

  vss_verify(share_i, vss_commitment)
    (i, sk_i) = share_i
    S_i = ScalarBaseMult(sk_i)
    S_i' = G.Identity()
    for j in range(0, MIN_PARTICIPANTS):
      S_i' += G.ScalarMult(vss_commitment[j], pow(i, j))
    if S_i == S_i':
      return 1
    return 0
~~~

We now define how the Coordinator and participants can derive group info,
which is an input into the FROST signing protocol.

~~~
    derive_group_info(MAX_PARTICIPANTS, MIN_PARTICIPANTS, vss_commitment):

    Inputs:
    - MAX_PARTICIPANTS, the number of shares to generate, an integer
    - MIN_PARTICIPANTS, the threshold of the secret sharing scheme, an integer
    - vss_commitment: A VSS commitment to a secret polynomial f, a vector commitment to each of the
    coefficients in coeffs, where each element of the vector commitment is an Element in G.

    Outputs:
    - PK, the public key representing the group, an Element.
    - participant_public_keys, a list of MAX_PARTICIPANTS public keys PK_i for i=1,...,MAX_PARTICIPANTS,
      where each PK_i is the public key, an Element, for participant i.

    derive_group_info(MAX_PARTICIPANTS, MIN_PARTICIPANTS, vss_commitment)
      PK = vss_commitment[0]
      participant_public_keys = []
      for i in range(1, MAX_PARTICIPANTS+1):
        PK_i = G.Identity()
        for j in range(0, MIN_PARTICIPANTS):
          PK_i += G.ScalarMult(vss_commitment[j], pow(i, j))
        participant_public_keys.append(PK_i)
      return PK, participant_public_keys
~~~

# Random Scalar Generation {#random-scalar}

Two popular algorithms for generating a random integer uniformly distributed in
the range \[0, G.Order() -1\] are as follows:

## Rejection Sampling

Generate a random byte array with `Ns` bytes, and attempt to map to a Scalar
by calling `DeserializeScalar` in constant time. If it succeeds, return the
result. If it fails, try again with another random byte array, until the
procedure succeeds. Failure to implement rejecting sampling in constant time can
leak information about the underlying corresponding Scalar.

Note the that the Scalar size might be some bits smaller than the array size,
which can result in the loop iterating more times than required. In that case
it's acceptable to set the high-order bits to 0 before calling `DeserializeScalar`,
but care must be taken to not set to zero more bits than required. For example,
in the `FROST(Ed25519, SHA-512)` ciphersuite, the order has 253 bits while
the array has 256; thus the top 3 bits of the last byte can be set to zero.

## Wide Reduction

Generate a random byte array with `l = ceil(((3 * ceil(log2(G.Order()))) / 2) / 8)`
bytes, and interpret it as an integer; reduce the integer modulo `G.Order()` and return the
result. See {{Section 5 of HASH-TO-CURVE}} for the underlying derivation of `l`.


# Test Vectors

This section contains test vectors for all ciphersuites listed in {{ciphersuites}}.
All `Element` and `Scalar` values are represented in serialized form and encoded in
hexadecimal strings. Signatures are represented as the concatenation of their
constituent parts. The input message to be signed is also encoded as a hexadecimal
string.

Each test vector consists of the following information.

- Configuration. This lists the fixed parameters for the particular instantiation
  of FROST, including MAX_PARTICIPANTS, MIN_PARTICIPANTS, and NUM_PARTICIPANTS.
- Group input parameters. This lists the group secret key and shared public key,
  generated by a trusted dealer as described in {{dep-dealer}}, as well as the
  input message to be signed. The randomly generated coefficients produced by the
  trusted dealer to share the group signing secret are also listed. Each coefficient
  is identified by its index, e.g., `share_polynomial_coefficients[1]` is the coefficient
  of the first term in the polynomial. Note that the 0-th coefficient is omitted as this
  is equal to the group secret key. All values are encoded as hexadecimal strings.
- Signer input parameters. This lists the signing key share for each of the
  NUM_PARTICIPANTS participants.
- Round one parameters and outputs. This lists the NUM_PARTICIPANTS participants engaged
  in the protocol, identified by their integer identifier, and for each participant:
  the hiding and binding commitment values produced in {{frost-round-one}}; the randomness
  values used to derive the commitment nonces in `nonce_generate`; the resulting group
  binding factor input computed in part from the group commitment list encoded as
  described in {{dep-encoding}}; and group binding factor as computed in {{frost-round-two}}).
- Round two parameters and outputs. This lists the NUM_PARTICIPANTS participants engaged
  in the protocol, identified by their integer identifier, along with their corresponding
  output signature share as produced in {{frost-round-two}}.
- Final output. This lists the aggregate signature as produced in {{frost-aggregation}}.

## FROST(Ed25519, SHA-512)

~~~
// Configuration information
MAX_PARTICIPANTS: 3
MIN_PARTICIPANTS: 2
NUM_PARTICIPANTS: 2

// Group input parameters
group_secret_key: 7b1c33d3f5291d85de664833beb1ad469f7fb6025a0ec78b3a7
90c6e13a98304
group_public_key: 15d21ccd7ee42959562fc8aa63224c8851fb3ec85a3faf66040
d380fb9738673
message: 74657374
share_polynomial_coefficients[1]: 178199860edd8c62f5212ee91eff1295d0d
670ab4ed4506866bae57e7030b204

// Signer input parameters
P1 participant_share: 929dcc590407aae7d388761cddb0c0db6f5627aea8e217f
4a033f2ec83d93509
P2 participant_share: a91e66e012e4364ac9aaa405fcafd370402d9859f7b6685
c07eed76bf409e80d
P3 participant_share: d3cb090a075eb154e82fdb4b3cb507f110040905468bb9c
46da8bdea643a9a02

// Round one parameters
participant_list: 1,3

// Signer round one outputs
P1 hiding_nonce_randomness: d90f5c52ad232cb07b7a2a39571569ae4777fcae3
7e79d5fb3ab25df36c9ac1d
P1 binding_nonce_randomness: 7743c8e1380dde8d7a3f55dd45f9446e4ea2387b
3e50c3ae7a7ba3c0df2b4e18
P1 hiding_nonce: 7fa76f778422a4df5e010ac0c18fe218a3390efb24bb03330920
fd9924e3cb00
P1 binding_nonce: 831ec501154719038355469f52a14826939076a2156d3a94c3d
dd1b5b1990101
P1 hiding_nonce_commitment: 225dc29a9ad6331c504f0c74ec1dd2f8f3d3caf51
c57d1507da660d5864dd111
P1 binding_nonce_commitment: 99a9a005570d0c4a2a1cdf8506f3f0bc4999f1bb
c1f0f4560db5fc10718e59c7
P1 binding_factor_input: 736c1aac57730ec200b2e1518606c711d9ea10906582
8e5ff26e81eb0247093047543440063365d5442a86234a8c9808720b77e094ace1f0c
924183e30605b860ddd9c473cec799c61cd1b27b299d92425552efab612816901bd09
6ca5177e4a6dca892d63e3e54104c3528cdff822844b1bf25c064726324e0a3c3a18a
eac9e0100000000000000000000000000000000000000000000000000000000000000
P1 binding_factor: a554199c0129d3e58aaa3e3dbb33ffc1dba39e42bcca7f9996
0a319598596c0a
P3 hiding_nonce_randomness: 843be54d5de6638a59ebc38f8d7252413e7bd2dd8
7535d13059355b97b838782
P3 binding_nonce_randomness: d075cdd90bee22f9b6e176a91c8c40f5f5749182
42d61d520348c548885c8e63
P3 hiding_nonce: d1d7b45226439f4ce52b0d3de2e39d187ef5d14df37a8b24edfe
14137ca7f702
P3 binding_nonce: 8c3b801ccee311ce227bbb7299316c987ab58332befeb1af962
514bfed5c2a05
P3 hiding_nonce_commitment: 32c5060098eeabd2ab610a1de01db8edf7817a280
6fae054eec3bf393eb02002
P3 binding_nonce_commitment: 5187b32260c101389cbd9388a13ea4a857c18ed5
7ddbfe5e2a8cd909687f0f02
P3 binding_factor_input: 736c1aac57730ec200b2e1518606c711d9ea10906582
8e5ff26e81eb0247093047543440063365d5442a86234a8c9808720b77e094ace1f0c
924183e30605b860ddd9c473cec799c61cd1b27b299d92425552efab612816901bd09
6ca5177e4a6dca892d63e3e54104c3528cdff822844b1bf25c064726324e0a3c3a18a
eac9e0300000000000000000000000000000000000000000000000000000000000000
P3 binding_factor: 0056040b9e32fba45431016edfc966f1520b51f687225e0eae
008c7999dad702

// Round two parameters
participant_list: 1,3

// Signer round two outputs
P1 sig_share: 8606c532b30cc00a43deec9168d99e30f92bc4bdda4654ac3311d6e
434e6b903
P3 sig_share: 1cc28c9fa85f88864467a8dc29f050da68815ef9341a4d8fdcf3985
f7ab00d06

sig: 73411ac2e43644e5f26dd69a4614a3112e4e38be173db08c4c4532ee6ed347d9
a2c851d25b6c48918745956e92c9ef0a62ad22b70f61a13b10056f44af96c709
~~~

## FROST(Ed448, SHAKE256)

~~~
// Configuration information
MAX_PARTICIPANTS: 3
MIN_PARTICIPANTS: 2
NUM_PARTICIPANTS: 2

// Group input parameters
group_secret_key: 6298e1eef3c379392caaed061ed8a31033c9e9e3420726f23b4
04158a401cd9df24632adfe6b418dc942d8a091817dd8bd70e1c72ba52f3c00
group_public_key: 3832f82fda00ff5365b0376df705675b63d2a93c24c6e81d408
01ba265632be10f443f95968fadb70d10786827f30dc001c8d0f9b7c1d1b000
message: 74657374
share_polynomial_coefficients[1]: dbd7a514f7a731976620f0436bd135fe8dd
dc3fadd6e0d13dbd58a1981e587d377d48e0b7ce4e0092967c5e85884d0275a7a740b
6abdcd0500

// Signer input parameters
P1 participant_share: 4a2b2f5858a932ad3d3b18bd16e76ced3070d72fd79ae44
02df201f525e754716a1bc1b87a502297f2a99d89ea054e0018eb55d39562fd0100
P2 participant_share: 2503d56c4f516444a45b080182b8a2ebbe4d9b2ab509f25
308c88c0ea7ccdc44e2ef4fc4f63403a11b116372438a1e287265cadeff1fcb0700
P3 participant_share: 00db7a8146f995db0a7cf844ed89d8e94c2b5f259378ff6
6e39d172828b264185ac4decf7219e4aa4478285b9c0eef4fccdf3eea69dd980d00

// Round one parameters
participant_list: 1,3

// Signer round one outputs
P1 hiding_nonce_randomness: 3021d3b4b48cb02c4ac620cf5d28d8b11bf22ed41
fad499ad9e2c2264b87ca56
P1 binding_nonce_randomness: 27a213f0ccf8e1bb7aa017ea4882549d1843ad48
3d940a7d1e293c86b109ab79
P1 hiding_nonce: 894a632445bfaa5a2e8fef7de281b3b60c6dc629aed28c18c1e4
c547e52ce5f6c5de40e21bfd319086a6de4a896f967edf12100b4a2a030000
P1 binding_nonce: 4b2db6069a22f5b7e1c1c02f07ca982d4736be62637a3964426
5c09930ac202bdaed67ab3296d4b72aada8c7c27d2fe99cb3deb4b557e50d00
P1 hiding_nonce_commitment: b5ccf8bce1f8c60ae6464286c20d5217e2da9b9f2
faa49223f30b3efb32115b6ddfec17aa913848bd65a0bcc3b061acbbdbb60ff63c236
ed00
P1 binding_nonce_commitment: 3ba50f19346e88bda231a98ad16da26cc930a3e8
183eac499b750f791bf1f63a2a6a8ecc17a9a301b41353e7c9d6fd6fedaee863662e8
fb300
P1 binding_factor_input: 80c3dfd62df16cc677ad6772d130badcd6dbd9754fd1
939a3db6252646088570c91470beec2cf5e32dac40f5ab582cbd21f538f48a69ad053
ffac2ddbb2c73e2b503edb94c3e86c1b71d114dda9980d87e7ce96172719c6de68869
f9552edcf4a909bb2010822c236cff0a52afb5e85f8971d04e8237355d8ee0b2ea992
dd789cb9c252079801169276cd169548ffc6e13e619114ac3f2765335c7dcaed4efce
2ccfa9f4af4de3cf9e751b67268f8b6cf3326f79cdff98c46aad74e08649c680b6b53
4c4eccff1fbae0716f47c09b8e51ed8ad3b2888cea73e048d90e35042a67fefb2e701
000000000000000000000000000000000000000000000000000000000000000000000
0000000000000000000000000000000000000000000
P1 binding_factor: 9d5b670675b6119fcd6e50a1e5d55801c1c626e7d1384b18dc
317facb1b25079f40fa6ba12f5bed14e79243c69d9f19dc49e7eafc6442f1000
P3 hiding_nonce_randomness: cecadb77769e98fc78bf9fd7ce03f84c2b0a99502
04ddd56e301c7402351f18d
P3 binding_nonce_randomness: 2dc2e8d4920361d6f1556e6ee4fc72f32cc65c96
0f18300a15e424d350a87f80
P3 hiding_nonce: c4f1213b76f99492fb7f9c29ce09d7e261265531e621887e62fd
caf085a3c7239a210f8a818dcdb0077f6329463ea299950a97bb4b10151a00
P3 binding_nonce: 748be96c1b78076407d672a09e0eeff33ed9fe4f27da80406bc
5b97aba9a8f2b1081b1bfbd2f70a4461fce2370ef977516f91cc8748b213800
P3 hiding_nonce_commitment: 7e6e4c2bb73a09956f78ce6ed53e560367493f22d
4bb90f53a9d8ef9a0d0a385653f6b03d4be761cbe076844dbca3f55e0a662d78ae2bf
4400
P3 binding_nonce_commitment: 1b03a0894e31a07648d7352b56f463ab4c97e1b5
ff8108ea6223b97b39c4fb798dbd38718d79bd2780740bf209d688401d5aa10b8259e
c5480
P3 binding_factor_input: 80c3dfd62df16cc677ad6772d130badcd6dbd9754fd1
939a3db6252646088570c91470beec2cf5e32dac40f5ab582cbd21f538f48a69ad053
ffac2ddbb2c73e2b503edb94c3e86c1b71d114dda9980d87e7ce96172719c6de68869
f9552edcf4a909bb2010822c236cff0a52afb5e85f8971d04e8237355d8ee0b2ea992
dd789cb9c252079801169276cd169548ffc6e13e619114ac3f2765335c7dcaed4efce
2ccfa9f4af4de3cf9e751b67268f8b6cf3326f79cdff98c46aad74e08649c680b6b53
4c4eccff1fbae0716f47c09b8e51ed8ad3b2888cea73e048d90e35042a67fefb2e703
000000000000000000000000000000000000000000000000000000000000000000000
0000000000000000000000000000000000000000000
P3 binding_factor: 7d67acba789ac3739c7cf8c7507513ef43e98ef079094838d3
d52057301aa7a9d33bbba8ec7db7d535b6a9d84d5eaa13b90aa3af5024c90900

// Round two parameters
participant_list: 1,3

// Signer round two outputs
P1 sig_share: e07f255fa86a4bbe6700cab2494bf2b932adf5d2065e2c6b5b7d3a3
9e066957a5dbec63d5ef79d0c1d4301e53cbfef32d76b6cf278a5c63f00
P3 sig_share: b99eb486b81ee28837e027e4590b01f0c1f5f3fa5d8dda177819a5c
3d483524b6d3ff47933de9e642c0635b1e798b19b73268e729c8f652a00

sig: 4311723e87464396c17f37055a57bf53b5cca4463bd53a7e933139663ba9c3e5
de1f0ef1085fc179d7247f0c54f83bc6ebe2d13e8a10c26d80a6d9813acec6b4234a5
12c0931948688646c131f1b10b8bee9721580b5eae7c5cafdbab791d53c7149493696
2458a1ce4a92fa6415352c2a00
~~~

## FROST(ristretto255, SHA-512)

~~~
// Configuration information
MAX_PARTICIPANTS: 3
MIN_PARTICIPANTS: 2
NUM_PARTICIPANTS: 2

// Group input parameters
group_secret_key: 1b25a55e463cfd15cf14a5d3acc3d15053f08da49c8afcf3ab2
65f2ebc4f970b
group_public_key: e2a62f39eede11269e3bd5a7d97554f5ca384f9f6d3dd9c3c0d
05083c7254f57
message: 74657374
share_polynomial_coefficients[1]: 410f8b744b19325891d73736923525a4f59
6c805d060dfb9c98009d34e3fec02

// Signer input parameters
P1 participant_share: 5c3430d391552f6e60ecdc093ff9f6f4488756aa6cebdba
d75a768010b8f830e
P2 participant_share: b06fc5eac20b4f6e1b271d9df2343d843e1e1fb03c4cbb6
73f2872d459ce6f01
P3 participant_share: f17e505f0e2581c6acfe54d3846a622834b5e7b50cad9a2
109a97ba7a80d5c04

// Round one parameters
participant_list: 1,3

// Signer round one outputs
P1 hiding_nonce_randomness: 78ffbd86443666a4a6c2dc9f4317a9d4ec89d71ad
3a849dc3db387aa7578366e
P1 binding_nonce_randomness: 451ff611af88b905c4077c0d5d96704bf3dd8e0a
f29e0370b472913f29e68ee1
P1 hiding_nonce: 1535263170cad41ca5967fd6c3d3340f882f312e9e504f049be8
e91658d75f0c
P1 binding_nonce: 4ba5452c9c4396a4c991e73c0599cca5acc6e56a50a5bff742e
10497fa86bf02
P1 hiding_nonce_commitment: aedc7adafd33fb483e1ec67c3b3e26a82ec0f5389
c02e029ba05af12e058cb1a
P1 binding_nonce_commitment: d2fc9a0fe50a482b333daeb50fc35fe737e59844
bf309f0008924964ee6c5f3c
P1 binding_factor_input: c70ac0b3effa113b8f4d8a6b1393ef7f0910862d143f
de83e410db94f3818295ff49ed5aed0e57b2712f2ce0f9166f1ffdce282786c7ee8c2
db2df295c61dc5f9a11e74948c9a85b2f8fe08e31fea0db99fb2987b9f89ce58e5763
5c8a21f2fd62887a4fe5dff91d006eee5f7582fe2fa203b9140ba9928eb2c5daab6db
d29250100000000000000000000000000000000000000000000000000000000000000
P1 binding_factor: 82b076e60e7bc2d9166e26513bd051537d22e439fcd9680fbc
7a4fe2f98f2c01
P3 hiding_nonce_randomness: 31fd92bfb10260843bb20d4126fe0800a6a8b53b0
96b8abcc6a4fe0ba328b35e
P3 binding_nonce_randomness: 841c5f6e8cfe0206d2c2ef5f1397fbc63f96336e
55bd3e5d3a191d7da01ad906
P3 hiding_nonce: 5e081268864c378515499016265616304010baee930387f717e4
6fb5f0b50c01
P3 binding_nonce: 39c499563105d66cf7b22473f4007c4b8581f03fe4a90e10fb5
b7d41cd570c05
P3 hiding_nonce_commitment: 2e2880c6d0f31d0a6bcd94c1166716fbcfc6b514b
0cff6916da1262ad22a1731
P3 binding_nonce_commitment: 281d9c41374b71ee6556db57355d9c3b9e463b06
643eadc7974f200254cec050
P3 binding_factor_input: c70ac0b3effa113b8f4d8a6b1393ef7f0910862d143f
de83e410db94f3818295ff49ed5aed0e57b2712f2ce0f9166f1ffdce282786c7ee8c2
db2df295c61dc5f9a11e74948c9a85b2f8fe08e31fea0db99fb2987b9f89ce58e5763
5c8a21f2fd62887a4fe5dff91d006eee5f7582fe2fa203b9140ba9928eb2c5daab6db
d29250300000000000000000000000000000000000000000000000000000000000000
P3 binding_factor: c936e361ff5663192298cf7d78c548e34283c2ebfd0c374e16
36cc758b2eef04

// Round two parameters
participant_list: 1,3

// Signer round two outputs
P1 sig_share: dfed66bb15c5ede3d6752082b62f6a7bd607a92d6754cb093822ba7
2d5445402
P3 sig_share: 823f6e89b1e3f90c7a594e0b95d1d29f466530990aae1ab9d8cf574
2144b7306

sig: ca39f58b4bbdf8e95a7e46c19a6b88a939cd3f9c9f8b57a722d3ea634fbf5435
612dd544c7a8e7f050cf6e8d4b013d1b1d6dd9c67102e6c210f211b5e98fc708
~~~

## FROST(P-256, SHA-256)

~~~
// Configuration information
MAX_PARTICIPANTS: 3
MIN_PARTICIPANTS: 2
NUM_PARTICIPANTS: 2

// Group input parameters
group_secret_key: 8ba9bba2e0fd8c4767154d35a0b7562244a4aaf6f36c8fb8735
fa48b301bd8de
group_public_key: 023a309ad94e9fe8a7ba45dfc58f38bf091959d3c99cfbd02b4
dc00585ec45ab70
message: 74657374
share_polynomial_coefficients[1]: 80f25e6c0709353e46bfbe882a11bdbb1f8
097e46340eb8673b7e14556e6c3a4

// Signer input parameters
P1 participant_share: 0c9c1a0fe806c184add50bbdcac913dda73e482daf95dcb
9f35dbb0d8a9f7731
P2 participant_share: 8d8e787bef0ff6c2f494ca45f4dad198c6bee01212d6c84
067159c52e1863ad5
P3 participant_share: 0e80d6e8f6192c003b5488ce1eec8f5429587d48cf00154
1e713b2d53c09d928

// Round one parameters
participant_list: 1,3

// Signer round one outputs
P1 hiding_nonce_randomness: 15ff7a70fcd257855ef9fadd54121036acb80a815
4e0b923bcdd07dc8b50b598
P1 binding_nonce_randomness: 75c4abe3da791884d8aee8a7d26f6abe4eecda98
92d6ddc1f72ed2cf475b93a7
P1 hiding_nonce: 3fb5dc9880401fd678a836def1781fcf419c05f518c5858f826b
9442eeb35134
P1 binding_nonce: ae2d8131bacf11422e78ffdb7a838828f65c3e072ed063d8c6e
f0294540ec79b
P1 hiding_nonce_commitment: 028faef0a9729ae2f82539c44f95bce366364bf63
7178bf004fc2e3a7f6728cd85
P1 binding_nonce_commitment: 03b93077e1dc34df20dd6cbaffe6d15a373e38d0
bbe4712d0890672e54de8ce9e5
P1 binding_factor_input: 47d0b1c45754dd58dc369bc4c1a9b24ffbb67ceb6d6e
25c302e9875202f7d2b4f18d456ca0e51bcb8c5f9c0e504e9909722154f9443fdd033
b352932dc36a162000000000000000000000000000000000000000000000000000000
0000000001
P1 binding_factor: 3ed07322b852ec0176c6ffe72f4d77d589cb0f827efaa69c6a
67cc8b144c144e
P3 hiding_nonce_randomness: b6e5b9b9011972b1883c55f78db1e4a18650f246a
f7107005e1b2b3b4edda14e
P3 binding_nonce_randomness: e72cc3707285c33070370c2458e42f90471e5b25
5cd57ec3c6d7a825876c3d7a
P3 hiding_nonce: e5b6c6ffaa464e0c59b0653bfee26519582e439f03f3ff256e38
cd439677e679
P3 binding_nonce: dbd6ae53eb3da1b65a2a1f5864d7f802a7dc467c0965aee85b8
4b0d0fff0bf1f
P3 hiding_nonce_commitment: 03dd3d824502d104c113b3663a4871675584110a1
44db7e0e04d281c653fd5c37c
P3 binding_nonce_commitment: 03c2fdcda396dd238bcd0e6e4118233a231ccb93
9d9d241ad5b994e2dd0254ef0d
P3 binding_factor_input: 47d0b1c45754dd58dc369bc4c1a9b24ffbb67ceb6d6e
25c302e9875202f7d2b4f18d456ca0e51bcb8c5f9c0e504e9909722154f9443fdd033
b352932dc36a162000000000000000000000000000000000000000000000000000000
0000000003
P3 binding_factor: 54a10fc42d0b8b0d6621f5708cc95307c88b3aa1f9032a24a1
a6af5e9dc6bcd8

// Round two parameters
participant_list: 1,3

// Signer round two outputs
P1 sig_share: e22b1c4991477d12bf3e49e862569a26c5405b6efdd0566299dd53d
7ebcdba37
P3 sig_share: a25fb8b16ac79a848edf2670b4f0f4c7cd77c2ce8befbabb1d211ae
82054678b

sig: 02f40acb8fdc1ffc8054e004f7d67bb35a8bf623edce1d7397a7ba65fb49a7b4
bc848ad4fbfc0f17964e1d705917478eeed5d1238fe2a87298c344a3fd0fbefc71
~~~

## FROST(secp256k1, SHA-256)

~~~
// Configuration information
MAX_PARTICIPANTS: 3
MIN_PARTICIPANTS: 2
NUM_PARTICIPANTS: 2

// Group input parameters
group_secret_key: 0d004150d27c3bf2a42f312683d35fac7394b1e9e318249c1bf
e7f0795a83114
group_public_key: 02f37c34b66ced1fb51c34a90bdae006901f10625cc06c4f646
63b0eae87d87b4f
message: 74657374
share_polynomial_coefficients[1]: fbf85eadae3058ea14f19148bb72b45e439
9c0b16028acaf0395c9b03c823579

// Signer input parameters
P1 participant_share: 08f89ffe80ac94dcb920c26f3f46140bfc7f95b493f8310
f5fc1ea2b01f4254c
P2 participant_share: 04f0feac2edcedc6ce1253b7fab8c86b856a797f44d83d8
2a385554e6e401984
P3 participant_share: 00e95d59dd0d46b0e303e500b62b7ccb0e555d49f5b849f
5e748c071da8c0dbc

// Round one parameters
participant_list: 1,3

// Signer round one outputs
P1 hiding_nonce_randomness: 9da0989746c5f595defcc05b39caa93d7b41cb240
6655a8a71ccb2aa70beaa40
P1 binding_nonce_randomness: 398e95c51270777c6d22e8a9bbc12b7417d63540
89a172447ba34aae17a22c95
P1 hiding_nonce: c505c534b61efe5bad654275fbf82d281995507398cccedbf21a
fe7e967aba2c
P1 binding_nonce: 6eb72d8d4f2a59aac800012438e9b97eab08b6ef4ecabe3dfed
0885be2030dc9
P1 hiding_nonce_commitment: 02e1b517ae4fbaa6e0cb4636eff030ab4d1f7248a
2a91f93d05b78e67d8212b783
P1 binding_nonce_commitment: 03caf8dd8e640f68b2a8fdeb45422d6f0745e315
2ecb4cc2951140a27204ba2c9f
P1 binding_factor_input: 8263cf41514645b3d57a9738502a0522c8d7b410ec42
b6ba8cca0830faacfa0166ca8ea442c5fd2f196a16fd685567dbb1fdfa22361e95539
a5ef5b5dc4ed9f5000000000000000000000000000000000000000000000000000000
0000000001
P1 binding_factor: d2bd62a579b91bc6c0c378cb1d7e110ce871ab2d9968550627
8e2f9c01fe54cf
P3 hiding_nonce_randomness: 28bd40efb56521126e4faaf118e9b826c8a2f8580
a2e6251235fce85def876a7
P3 binding_nonce_randomness: ef03531ea324e11b5f4b22ca3ba7c3cbf834afd4
5d93337d033e768bd1c1515b
P3 hiding_nonce: 9f299bfad016596fcca42feb8fce6be5b6ee5bdf3f12a06837ec
8d4364308215
P3 binding_nonce: 732e7aa3d4f7619b4f7e30e1717bf0d58a3b7b0d89680185b6c
76cc0347a8565
P3 hiding_nonce_commitment: 0209ae226d3ff6b28984005cdfe56d71acfd2de10
5a83312f4d23a2da83d675b63
P3 binding_nonce_commitment: 02338c59ea5e12dff38a6208d7eaa8c8714db695
eef1f2e07a2c34bdb51ea5ee6f
P3 binding_factor_input: 8263cf41514645b3d57a9738502a0522c8d7b410ec42
b6ba8cca0830faacfa0166ca8ea442c5fd2f196a16fd685567dbb1fdfa22361e95539
a5ef5b5dc4ed9f5000000000000000000000000000000000000000000000000000000
0000000003
P3 binding_factor: e8026d8ee5f03798234bbfbefdcac22303e17f62b80a70b261
49e429b8e755d8

// Round two parameters
participant_list: 1,3

// Signer round two outputs
P1 sig_share: 91fcddc34dd3c9bb6682a308b024db10d2fad961a70383f0b89ca1d
8455c15cb
P3 sig_share: 77a34600717728b1b25d335a438aa92e9f8539e1f1cdf95b8336fed
ef350b934

sig: 0273f8db2ce27553cb82bae745a53a90559584592d08279f43ab84015cdee5cd
0a09a023c3bf4af26d18dfd662f3af8440b7d1365ce988dd107c01422a68768dbe
~~~
