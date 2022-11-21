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
  Pornin22:
    target: https://eprint.iacr.org/2022/1164.pdf
    title: "Point-Halving and Subgroup Membership in Twisted Edwards Curves"
    author:
      - name: Thomas Pornin
    date: 2022-09-06

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

draft-11

- Update version string constant (#307)
- Make SerializeElement reject the identity element (#306)
- Make ciphersuite requirements explicit (#302)
- Fix various editorial issues (#303, #301, #299, #297)

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
* `encode_uint16(x)`: Convert two byte unsigned integer (uint16) x to
a 2-byte, big-endian byte string.  For example, `encode_uint16(310) = [0x01, 0x36]`.
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

- Order(): Outputs the order of `G` (i.e. `p`).
- Identity(): Outputs the identity `Element` of the group (i.e. `I`).
- RandomScalar(): Outputs a random `Scalar` element in GF(p), i.e., a random scalar in \[0, p - 1\].
- ScalarMult(A, k): Output the scalar multiplication between Element `A` and Scalar `k`.
- ScalarBaseMult(k): Output the scalar multiplication between Scalar `k` and the group generator `B`.
- SerializeElement(A): Maps an `Element` `A` to a canonical byte array `buf` of fixed length `Ne`. This
  function can raise an error if `A` is the identity element of the group.
- DeserializeElement(buf): Attempts to map a byte array `buf` to an `Element` `A`,
  and fails if the input is not the valid canonical byte representation of an element of
  the group. This function can raise an error if deserialization fails
  or `A` is the identity element of the group; see {{ciphersuites}} for group-specific
  input validation steps.
- SerializeScalar(s): Maps a Scalar `s` to a canonical byte array `buf` of fixed length `Ns`.
- DeserializeScalar(buf): Attempts to map a byte array `buf` to a `Scalar` `s`.
  This function can raise an error if deserialization fails; see
  {{ciphersuites}} for group-specific input validation steps.

## Cryptographic Hash Function {#dep-hash}

FROST requires the use of a cryptographically secure hash function, generically
written as H, which functions effectively as a random oracle. For concrete
recommendations on hash functions which SHOULD be used in practice, see
{{ciphersuites}}. Using H, we introduce separate domain-separated hashes,
H1, H2, H3, H4, H5, and H6:

- H1, H2, H3, and H4 map arbitrary byte strings to Scalar elements of the prime-order group scalar field.
- H5 and H6 are aliases for H with distinct domain separators.

The details of H1, H2, H3, H4, H5, and H6 vary based on ciphersuite. See {{ciphersuites}}
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
with the secret key as input to a domain-separated hash function built
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
      if count(x_j, L) > 1:
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
    msg_hash = H5(msg)
    encoded_commitment_hash = H6(encode_group_commitment_list(commitment_list))
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

FROST assumes that the Coordinator and the set of signer participants, are chosen
externally to the protocol. Note that it is possible to deploy the protocol without
a distinguished Coordinator; see {{no-coordinator}} for more information.

FROST produces signatures that are indistinguishable from those produced with a single
participant using a signing key `s` with corresponding public key `PK`, where `s` is a Scalar
value and `PK = G.ScalarBaseMult(s)`. As a threshold signing protocol, the group signing
key `s` is secret-shared amongst each participant and used to produce signatures. In particular,
FROST assumes each participant is configured with the following information:

- An identifier, which is a Scalar value denoted `i` in the range `[1, MAX_PARTICIPANTS]`
  and MUST be distinct from the identifier of every other participant.
- A signing key share `sk_i`, which is a Scalar value representing the i-th secret share
  of the group signing key `s`. The public key corresponding to this signing key share
  is `PK_i = G.ScalarBaseMult(sk_i)`.

The Coordinator and each participant are additionally configured with common group
information, denoted "group info," which consists of the following:

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
the two rounds, and this state is deleted as described in {{frost-round-two}}. The final
Aggregation step is described in {{frost-aggregation}}.

FROST assumes that all inputs to each round, especially those of which are received
over the network, are validated before use. In particular, this means that any value
of type Element or Scalar is deserialized using DeserializeElement and DeserializeScalar,
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
the public output `comm` is sent to the Coordinator. The nonce values produced by this
function MUST NOT be reused in more than one invocation of FROST, and it MUST be generated
from a source of secure randomness.

<!-- The Coordinator must not get confused about which commitments come from which signers, do we need to say more about how this is done? -->

## Round Two - Signature Share Generation {#frost-round-two}

In round two, the Coordinator is responsible for sending the message to be signed, and
for choosing which participants will participate (of number at least MIN_PARTICIPANTS). Signers
additionally require locally held data; specifically, their private key and the
nonces corresponding to their commitment issued in round one.

The Coordinator begins by sending each participant the message to be signed along with the
set of signing commitments for all participants in the participant list. Each participant
MUST validate the inputs before processing the Coordinator's request. In particular,
the Signer MUST validate commitment_list, deserializing each group Element in the
list using DeserializeElement from {{dep-pog}}. If deserialization fails, the Signer
MUST abort the protocol. Moreover, each participant MUST ensure that
their identifier appears in commitment_list along with
their commitment from the first round.
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
signature share using DeserializeElement. If validation fails, the Coordinator MUST abort
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
particular prime-order group corresponding to a ciphersuite MUST adhere
to the description in {{dep-pog}}. Validation steps for these functions
are described for each the ciphersuites below. Future ciphersuites MUST
describe how input validation is done for DeserializeElement and DeserializeScalar.

Each ciphersuite includes explicit instructions for verifying signatures produced
by FROST. Note that these instructions are equivalent to those produced by a single
participant.

Each ciphersuite adheres to the requirements in {{ciphersuite-reqs}}. Future
ciphersuites MUST also adhere to these requirements.

## FROST(Ed25519, SHA-512)

This ciphersuite uses edwards25519 for the Group and SHA-512 for the Hash function `H`
meant to produce signatures indistinguishable from Ed25519 as specified in {{!RFC8032}}.
The value of the contextString parameter is "FROST-ED25519-SHA512-v11".

- Group: edwards25519 {{!RFC8032}}
  - Order(): Return 2^252 + 27742317777372353535851937790883648493 (see {{?RFC7748}})
  - Identity(): As defined in {{RFC7748}}.
  - RandomScalar(): Implemented by returning a uniformly random Scalar in the range
    \[0, `G.Order()` - 1\]. Refer to {{random-scalar}} for implementation guidance.
  - SerializeElement(A): Implemented as specified in {{!RFC8032, Section 5.1.2}}.
    Additionally, this function validates that the input element is not the group
    identity element.
  - DeserializeElement(buf): Implemented as specified in {{!RFC8032, Section 5.1.3}}.
    Additionally, this function validates that the resulting element is not the group
    identity element and is in the prime-order subgroup. The latter check can
    be implemented by multiplying the resulting point by the order of the group and
    checking that the result is the identity element. Note that optimizations for
    this check exist; see {{Pornin22}}.
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
  - H4(m): Implemented by computing H("poly" \|\| m), interpreting the 64-byte digest
    as a little-endian integer, and reducing the resulting integer modulo
    2^252+27742317777372353535851937790883648493.
  - H5(m): Implemented by computing H(contextString \|\| "msg" \|\| m).
  - H6(m): Implemented by computing H(contextString \|\| "com" \|\| m).


Normally H2 would also include a domain separator, but for backwards compatibility
with {{!RFC8032}}, it is omitted.

Signature verification is as specified in {{Section 5.1.7 of RFC8032}} with the
constraint that implementations MUST check the group equation [8][S]B = [8]R + [8][k]A'.
The alternative check [S]B = R + [k]A' is not safe or interoperable in practice.

## FROST(ristretto255, SHA-512) {#recommended-suite}

This ciphersuite uses ristretto255 for the Group and SHA-512 for the Hash function `H`.
The value of the contextString parameter is "FROST-RISTRETTO255-SHA512-v11".

- Group: ristretto255 {{!RISTRETTO=I-D.irtf-cfrg-ristretto255-decaf448}}
  - Order(): Return 2^252 + 27742317777372353535851937790883648493 (see {{RISTRETTO}})
  - Identity(): As defined in {{RISTRETTO}}.
  - RandomScalar(): Implemented by returning a uniformly random Scalar in the range
    \[0, `G.Order()` - 1\]. Refer to {{random-scalar}} for implementation guidance.
  - SerializeElement(A): Implemented using the 'Encode' function from {{!RISTRETTO}}.
    Additionally, this function validates that the input element is not the group
    identity element.
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
  - H4(m): Implemented by computing H("poly" \|\| m) and mapping the
    output to a Scalar as described in {{!RISTRETTO, Section 4.4}}.
  - H5(m): Implemented by computing H(contextString \|\| "msg" \|\| m).
  - H6(m): Implemented by computing H(contextString \|\| "com" \|\| m).

Signature verification is as specified in {{prime-order-verify}}.

## FROST(Ed448, SHAKE256)

This ciphersuite uses edwards448 for the Group and SHAKE256 for the Hash function `H`
meant to produce signatures indistinguishable from Ed448 as specified in {{!RFC8032}}.
The value of the contextString parameter is "FROST-ED448-SHAKE256-v11".

- Group: edwards448 {{!RFC8032}}
  - Order(): Return 2^446 - 13818066809895115352007386748515426880336692474882178609894547503885
  - Identity(): As defined in {{RFC7748}}.
  - RandomScalar(): Implemented by returning a uniformly random Scalar in the range
    \[0, `G.Order()` - 1\]. Refer to {{random-scalar}} for implementation guidance.
  - SerializeElement(A): Implemented as specified in {{!RFC8032, Section 5.2.2}}.
    Additionally, this function validates that the input element is not the group
    identity element.
  - DeserializeElement(buf): Implemented as specified in {{!RFC8032, Section 5.2.3}}.
    Additionally, this function validates that the resulting element is not the group
    identity element and is in the prime-order subgroup. The latter check can
    be implemented by multiplying the resulting point by the order of the group and
    checking that the result is the identity element. Note that optimizations for
    this check exist; see {{Pornin22}}.
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
  - H4(m): Implemented by computing H("poly" \|\| m), interpreting the
    114-byte digest as a little-endian integer, and reducing the resulting integer modulo
    2^446 - 13818066809895115352007386748515426880336692474882178609894547503885.
  - H5(m): Implemented by computing H(contextString \|\| "msg" \|\| m).
  - H6(m): Implemented by computing H(contextString \|\| "com" \|\| m).

Normally H2 would also include a domain separator, but for backwards compatibility
with {{!RFC8032}}, it is omitted.

Signature verification is as specified in {{Section 5.2.7 of RFC8032}} with the
constraint that implementations MUST check the group equation [4][S]B = [4]R + [4][k]A'.
The alternative check [S]B = R + [k]A' is not safe or interoperable in practice.

## FROST(P-256, SHA-256)

This ciphersuite uses P-256 for the Group and SHA-256 for the Hash function `H`.
The value of the contextString parameter is "FROST-P256-SHA256-v11".

- Group: P-256 (secp256r1) {{x9.62}}
  - Order(): Return 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
  - Identity(): As defined in {{x9.62}}.
  - RandomScalar(): Implemented by returning a uniformly random Scalar in the range
    \[0, `G.Order()` - 1\]. Refer to {{random-scalar}} for implementation guidance.
  - SerializeElement(A): Implemented using the compressed Elliptic-Curve-Point-to-Octet-String
    method according to {{SEC1}}, yielding a 33 byte output. Additionally, this function validates
    that the input element is not the group identity element.
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
  - H4(m): Implemented as hash_to_field(m, 1) from {{!HASH-TO-CURVE, Section 5.2}}
    using `expand_message_xmd` with SHA-256 with parameters DST = "poly",
    F set to the scalar field, p set to `G.Order()`, m = 1, and L = 48.
  - H5(m): Implemented by computing H(contextString \|\| "msg" \|\| m).
  - H6(m): Implemented by computing H(contextString \|\| "com" \|\| m).

Signature verification is as specified in {{prime-order-verify}}.

## FROST(secp256k1, SHA-256)

This ciphersuite uses secp256k1 for the Group and SHA-256 for the Hash function `H`.
The value of the contextString parameter is "FROST-secp256k1-SHA256-v11".

- Group: secp256k1 {{SEC2}}
  - Order(): Return 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
  - Identity(): As defined in {{SEC2}}.
  - RandomScalar(): Implemented by returning a uniformly random Scalar in the range
    \[0, `G.Order()` - 1\]. Refer to {{random-scalar}} for implementation guidance.
  - SerializeElement(A): Implemented using the compressed Elliptic-Curve-Point-to-Octet-String
    method according to {{SEC1}}. Additionally, this function validates that the input element
    is not the group identity element.
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
  - H4(m): Implemented as hash_to_field(m, 1) from {{!HASH-TO-CURVE, Section 5.2}}
    using `expand_message_xmd` with SHA-256 with parameters DST = "poly",
    F set to the scalar field, p set to `G.Order()`, m = 1, and L = 48.
  - H5(m): Implemented by computing H(contextString \|\| "msg" \|\| m).
  - H6(m): Implemented by computing H(contextString \|\| "com" \|\| m).

Signature verification is as specified in {{prime-order-verify}}.

## Ciphersuite Requirements {#ciphersuite-reqs}

Future documents that introduce new ciphersuites MUST adhere to
the following requirements.

1. H1, H2, and H3 all have output distributions that are close to
  (indistinguishable from) the uniform distribution.
2. All hash functions MUST be domain separated with a per-suite context
  string. Note that the FROST(Ed25519, SHA-512) ciphersuite does not
  adhere to this requirement for backwards compatibility with {{RFC8032}}.
3. The group MUST be of prime-order, and all deserialization functions MUST
  output elements that belong to to their respective sets of Elements or Scalars,
  or failure when deserialization fails.

# Security Considerations {#sec-considerations}

A security analysis of FROST exists in {{FROST20}} and {{Schnorr21}}. The protocol as specified
in this document assumes the following threat model.

* Secure key distribution. The signer key shares are generated and distributed securely, i.e.,
via a trusted dealer that performs key generation (see {{dep-vss}}) or through a distributed
key generation protocol.

* Honest-but-curious coordinator. We assume an honest-but-curious Coordinator which, at the
time of signing, does not perform a denial of service attack. A denial of service would include
any action which either prevents the protocol from completing or causing the resulting signature
to be invalid. Such actions for the latter include sending inconsistent values to participants,
such as messages or the set of individual commitments. Note that the Coordinator
is *not* trusted with any private information and communication at the time of signing
can be performed over a public but reliable channel.

Under this threat model, FROST aims to achieve signature unforgeability assuming at most
`(MIN_PARTICIPANTS-1)` corrupted participants. In particular, so long as an adversary corrupts
fewer than `MIN_PARTICIPANTS` participants, the scheme remains secure against Existential
Unforgeability Under Chosen Message Attack (EUF-CMA) attacks, as defined in {{BonehShoup}},
Definition 13.2. Satisfying this requirement requires the ciphersuite to adhere to the
requirements in {{ciphersuite-reqs}}.

FROST does not aim to achieve the following goals:

* Post quantum security. FROST, like plain Schnorr signatures, requires the hardness of the Discrete Logarithm Problem.
* Robustness. In the case of failure, FROST requires aborting the protocol.
* Downgrade prevention. All participants in the protocol are assumed to agree on what algorithms to use.
* Metadata protection. If protection for metadata is desired, a higher-level communication
channel can be used to facilitate key generation and signing.

The rest of this section documents issues particular to implementations or deployments.

## Nonce Reuse Attacks

{{dep-nonces}} describes the procedure that participants use to produce nonces during
the first round of signing. The randomness produced in this procedure MUST be sampled
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
(`H`) associated with the chosen ciphersuite in a manner similar to how `H5` is defined.
In particular, a different prefix SHOULD be used to differentiate this pre-hash from
`H5`. One possible example is to construct this pre-hash over message `m` as
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

This section contains descriptions of functions for generating and verifying Schnorr signatures.
It is included to complement the routines present in {{RFC8032}} for prime-order groups, including
ristretto255, P-256, and secp256k1. The functions for generating and verifying signatures are
`prime_order_sign` and `prime_order_verify`, respectively.

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
between the secret key `s` and the `MAX_SIGNER` secret shares is formalized in the
`secret_share_combine(shares, MIN_PARTICIPANTS)` algorithm, defined in {{dep-shamir}}.

The dealer that performs `trusted_dealer_keygen` is trusted to 1) generate good randomness,
and 2) delete secret values after distributing shares to each participant, and 3) keep
secret values confidential.

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
    poly_randomness = random_bytes(32)
    participant_private_keys = secret_share_shard(secret_key, poly_randomness, MIN_PARTICIPANTS, MAX_PARTICIPANTS)
    coefficients = secret_share_polynomial(secret_key, poly_randomness, MIN_PARTICIPANTS)
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

A single share of a secret with threshold `t` is generated using the following function.

~~~
  secret_share_sample(s, r, t, x):

  Inputs:
  - s, secret value to be shared, a Scalar
  - r, a seed used to derive the secret sharing polynomial, a 32-byte string
  - t, the threshold for the secret sharing scheme, an integer less than 2^16
  - x, the point at which to produce a secret, a Scalar

  Outputs:
  - y, A share of the secret corresponding to the input point x

  Errors:
  - "invalid parameters", if t is less than 2

  def secret_share_sample(s, r, t, x):
    if t < 2:
      raise "invalid parameters"

    # Construct and evaluate the polynomial at point x
    polynomial_coefficients = secret_share_polynomial(s, r, t)
    y = polynomial_evaluate(x, polynomial_coefficients)

    return y
~~~

The helper function secret_share_polynomial is defined as follows.

~~~
  secret_share_polynomial(s, r, t):

  Inputs:
  - s, secret value to be shared, a Scalar
  - r, a seed used to derive the secret sharing polynomial, a 32-byte string
  - t, the threshold for the secret sharing scheme, an integer less than 2^16

  Outputs:
  - polynomial_coefficients, the list of secret sharing polynomial coefficients
    in increasing order, each a Scalar

  Errors:
  - "invalid parameters", if t is less than 2

  def secret_share_polynomial(s, r, t):
    if t < 2:
      raise "invalid parameters"

    # Construct the polynomial from the random seed and threshold count
    polynomial_coefficients = [s]
    for i in range(0, t - 1):
      coefficient = H4(r || encode_uint16(i))
      polynomial_coefficients.append(coefficient)

    return polynomial_coefficients
~~~

Using secret_share_sample, the procedure for splitting a secret into some positive
integer `n` shares with a threshold of size `t` is as follows.

~~~
  secret_share_shard(s, r, t, n):

  Inputs:
  - s, secret value to be shared, a Scalar
  - r, a seed used to derive the secret sharing polynomial, a 32-byte string
  - t, the threshold for the secret sharing scheme, an integer less than 2^16
  - n, the number of shares to generate, an integer less than 2^16

  Outputs:
  - secret_key_shares, A list of secret shares, each a tuple of two Scalar values

  Errors:
  - "invalid parameters", if t > n or if t is less than 2

  def secret_share_shard(s, r, t, n):
    if t > n:
      raise "invalid parameters"
    if t < 2:
      raise "invalid parameters"

    # Evaluate the polynomial for each point x=1,...,n
    secret_key_shares = []
    for x_i in range(1, n + 1):
      y_i = secret_share_sample(s, r, t, Scalar(x_i))
      secret_key_share_i = (x_i, y_i)
      secret_key_share.append(secret_key_share_i)
    return secret_key_shares
~~~

Let `points` be the output of secret_share_shard. The i-th element in `points` is
the share for the i-th participant, which is the randomly generated polynomial
evaluated at coordinate `i`. We denote a secret share as the tuple `(i, points[i])`,
and the list of these shares as `shares`. `i` MUST never equal `0`; recall that
`f(0) = s`, where `f` is the polynomial defined in a Shamir secret sharing operation.

The procedure for combining a `shares` list of length at least thresold `t` to recover the
secret `s` is as follows; the algorithm `polynomial_interpolation` is defined in {{dep-polynomial-interpolate}}.

~~~
  secret_share_combine(shares, t):

  Inputs:
  - shares, a list of at minimum t secret shares, each a tuple (i, f(i))
    where i and f(i) are Scalars
  - t, a threshold

  Outputs: The resulting secret s, a Scalar, that was previously split into shares

  Errors:
  - "invalid parameters", if fewer than t input shares are provided

  def secret_share_combine(shares, t):
    if len(shares) < t:
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

The procedure for committing to a polynomial `f` is as follows.

~~~
  vss_commit(coefficients):

  Inputs:
  - coefficients, a vector of the coefficients which uniquely determine a polynomial f.

  Outputs: a commitment vss_commitment, which is a vector commitment to each of the
  coefficients in coeffs, where each element of the vector commitment is an Element in G.

  def vss_commit(coefficients):
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
    (x_i, y_i) = share_i
    S_i = ScalarBaseMult(y_i)
    S_i' = G.Identity()
    for j in range(0, MIN_PARTICIPANTS):
      S_i' += G.ScalarMult(vss_commitment[j], pow(x_i, j))
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
procedure succeeds. Failure to implement `DeserializeScalar` in constant time
can leak information about the underlying corresponding Scalar.

As an optimization, if the group order is very close to a power of
2, it is acceptable to omit the rejection test completely.  In
particular, if the group order is p, and there is an integer b
such that `p - 2<sup>b</sup>| < 2<sup>(b/2)</sup>`, then
`RandomScalar` can simply return a uniformly random integer of at
most b bits.

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
  input message to be signed. The random bytes produced by the trusted dealer
  for deriving the secret sharing polynomial is also listed.
  All values are encoded as hexadecimal strings.
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
share_polynomial_randomness: 4915449839ca3d3f467a9900b26e7996be2e024d
e91e74730894792bc1141ad3

// Signer input parameters
P1 participant_share: eacab4eec9194c232d455a854ba2d085aa8a2a41d05f22b
81878232c5f047e05
P2 participant_share: 5979360a9e097bc17b236cd7d892f3c4b5959e7f46b17de
4f6763aeaaa5f7806
P3 participant_share: c827b82572f9a95fca017e2966831604c1a012bebc02d91
0d57551a8f6ba7207

// Round one parameters
participant_list: 1,3

// Signer round one outputs
P1 hiding_nonce_randomness: aa94f9972fc7d8ca4ad7ec5528c0a2582ede34b92
2a632f9701ccb6126c96351
P1 binding_nonce_randomness: 73a7a203bfe98d75ce484585d54e75397c2cb2e0
35697d08032a45b6bdd8e48f
P1 hiding_nonce: dfcb46771e4e4e6fbc9ff30ad3360b2306ce603e277d97c9fb56
000aea638b0f
P1 binding_nonce: 765d63e499f9d66ffc4d1259d60f812b46978cdeff4968dd2f6
38233803c7706
P1 hiding_nonce_commitment: 79b8210eb01b3711ae8720002280ba3a90b739b5f
641cdb6bb4e312f1c6473b8
P1 binding_nonce_commitment: 846af5780a15b1ede515513459e5b6102cae693c
826df4b34d6c8b3800553c75
P1 binding_factor_input: c5b95020cba31a9035835f074f718d0c3af02a318d6b
4723bbd1c088f4889dd7b9ff8e79f9a67a9d27605144259a7af18b7cca2539ffa5c4f
1366a98645da8f4e463dedb11dc087e5ccab2a56f3a52776b731ad7230bc2dd0ac4bf
fc189913c275c4f5b122e93b6c9da9bb8a6dc8c4c08607f42d089470a174ad95168e3
ac0060100000000000000000000000000000000000000000000000000000000000000
P1 binding_factor: 5eee0b1eeab919bd9b532ccb9d963bcf37c161e2fa5df7d484
a775a4144ea108
P3 hiding_nonce_randomness: fbcf3fbb04ec7bc609d3a23041b0aff38b49d7496
22cabb2531ff8a219f3af74
P3 binding_nonce_randomness: 64f2c449e7f84729fca5e173d3bbf5923a044a40
8924e5142f944b0cf32c6bb0
P3 hiding_nonce: 79e90e70b47838297ea7f5ddf374d46b7a13ff6efa987c62f083
2fecebc0620b
P3 binding_nonce: eff0143b9eb56159c5f9d159fbc286b2960eb31ed0a6f6ae43f
63c77da09560e
P3 hiding_nonce_commitment: d47817cfdb06b60693704fdc57496f98b9dd71d5e
d805815e1a04d09125b913b
P3 binding_nonce_commitment: e56945e4979cd3c3efb023771ea143fb19c72292
db528720903378ec42bae9b8
P3 binding_factor_input: c5b95020cba31a9035835f074f718d0c3af02a318d6b
4723bbd1c088f4889dd7b9ff8e79f9a67a9d27605144259a7af18b7cca2539ffa5c4f
1366a98645da8f4e463dedb11dc087e5ccab2a56f3a52776b731ad7230bc2dd0ac4bf
fc189913c275c4f5b122e93b6c9da9bb8a6dc8c4c08607f42d089470a174ad95168e3
ac0060300000000000000000000000000000000000000000000000000000000000000
P3 binding_factor: 4061f7911c0d39c569aff9be2ae372455ebf69090afaca00a0
e8064209ee4502

// Round two parameters
participant_list: 1,3

// Signer round two outputs
P1 sig_share: 21ac4746d9c027b31a493122ee9456c288f590a3263962b25dfc8b0
455aad90f
P3 sig_share: dd3fe7a11dc6472fd99fb68c86ccb9d1008a019474acf47b8009224
d44fd470c

sig: 1186bc539b8ff6f5594b5c2d5523057efd74902ce95e6c8890a32ff8a1e8b744
1118398bdc235d8a1d4cf00b9667317f897f92379be5562ede05ae5199a7210c
~~~

## FROST(Ed448, SHAKE256)

~~~
// Configuration information
MAX_PARTICIPANTS: 3
MIN_PARTICIPANTS: 2
NUM_PARTICIPANTS: 2

// Group input parameters
group_secret_key: d30d44059553bd35c3877029eb2e53cb75fbb66757173aeb7d8
3e2cf1dff7ba2dfdbe583fdbb4c1ed0bc1dbaad6bba68ca67a695d2e99d0a00
group_public_key: 6ee1742e481978de531c5e0533817bf6f941a6f7704511269ed
ae7dbd24ed9eec513b14d72be0da28bc87c8da7faccf5f233420ff7978bff00
message: 74657374
share_polynomial_randomness: 0944cb89086741f63dbf88658781374ae0251c11
85461a8230a83b471a64eeb6

// Signer input parameters
P1 participant_share: dcf0d7ecf6339a00322ba8b58158287571446b2b78796d9
9c7b03e6024b6443c896afeeae5dc8c9749d07e9428b3108a42acbcd3351c230300
P2 participant_share: d818c47febd6efeef55da5cf8a446a40fdc3f59de2b6ef0
bfb01656d2a6d0dd632f91652cefdcc10c3e3df6ea3fa66abbaf0d211994ea83b00
P3 participant_share: e1fb57674db7ccb96401dd5b216e3feaf80caa61031923b
a442fc1fd3024d66fdc872fb9b61e0d8a3cf740491e42bdcc3235e94ffc802d3400

// Round one parameters
participant_list: 1,3

// Signer round one outputs
P1 hiding_nonce_randomness: f058a8d09dc1c95bfa22f1422a062a3aa1a726c86
03d5cd481f5159213ccc6ef
P1 binding_nonce_randomness: 7b2135e7b2ae34fe66abbda7b0c87121f687adf8
ce58afb9aaef60700e7fa8f4
P1 hiding_nonce: a22cd7f5c995450cc10a6c8c71585e5e394de40703ae14cc2ddf
a1f1ed25f6713b4cbde0804fa96e1e8aaea9691b970ce9335983cf0e5f2600
P1 binding_nonce: 83222fce0a18048cc7f5be82094f26cdff54dd0066b42e89bdb
8e2db0135324d12be60ba3d91d0dd8c65dfd9ba0e82d9eeb001e05d14421a00
P1 hiding_nonce_commitment: 5588a47798579acfd80dbf146302b4756ac519e07
256c3ed42ce8673c82b11d881a058696d14547748029b07a34d2e44687f8b8c54fc8e
3b80
P1 binding_nonce_commitment: 2a9be248ac72e9dca8f2c925d284869339829045
5a19e9fb4293b06ddcdd1607e47cc4d7c71981563a9baa75bac13f779ae13c9aafdc5
b1c00
P1 binding_factor_input: 106dadce87ca867018702d69a02effd165e1ac1a511c
957cff1897ceff2e34ca212fe798d84f0bde6054bf0fa77fd4cd4bc4853d6dc8dbd19
d340923f0ebbbb35172df4ab865a45d55af31fa0e6606ea97cf8513022b2b133d0f9f
6b8d3be184221fc4592bf12bd7fb4127bb67e51a6dc9e5ac5482f915ffc8a690d471d
b5a453aaf462d2cdf4bedf5e65d91b6991fe29fea8790f84cf29ce6e276e20386ecc7
f216798d3c1687a282c7dbb055857bb3eb386f5aaea36c37a5cac9e737c11ea653563
3e937ac2a351dc3fae28ced2e82e7824c386e4918a839baa9025a7afa524e6102c101
000000000000000000000000000000000000000000000000000000000000000000000
0000000000000000000000000000000000000000000
P1 binding_factor: fa14369a6ab8c34fa5113726593b772289e4f461d14ab2edb2
9787f09ac0b35c179195c7f85c66fd621c7a0d7eb6beff107c893aa70c773800
P3 hiding_nonce_randomness: c04b3ff9a28f6a7e42d954c6bceccb696cc38b503
3277d7c3abba8f164aa2643
P3 binding_nonce_randomness: 38ec469321d84f2c1fceea93b53bb4979a9f06f7
a66f512019610f7f6c606b32
P3 hiding_nonce: 4dd2154c9eac289161355fdcb614947d586f7abe12e02e38a455
a9f1ff600249f6cd3d5ca138e365b17c0c67b594b05fcf05b8bdf5aac60f00
P3 binding_nonce: 8de806c67a5772396b4d8957db49a313930da68f7a8f647c24a
9135ef254c0ea6a459636e410e56b5d9a9b9633ed8a11ef023a972f32392f00
P3 hiding_nonce_commitment: 5d568d69d05e52dc8e54192f5cea50426eb08172f
880b4b14a48691908494bf38419ec8fa260e6e02f664dc091a9903713ded5407bea10
2d80
P3 binding_nonce_commitment: d80f90afec314f6a36fd80af033a6b655b292a49
f92fed42a91fbd6fb7b392f5a75b53474fb8e52b866f53c9ca057fb6439743e6d6ea4
b0200
P3 binding_factor_input: 106dadce87ca867018702d69a02effd165e1ac1a511c
957cff1897ceff2e34ca212fe798d84f0bde6054bf0fa77fd4cd4bc4853d6dc8dbd19
d340923f0ebbbb35172df4ab865a45d55af31fa0e6606ea97cf8513022b2b133d0f9f
6b8d3be184221fc4592bf12bd7fb4127bb67e51a6dc9e5ac5482f915ffc8a690d471d
b5a453aaf462d2cdf4bedf5e65d91b6991fe29fea8790f84cf29ce6e276e20386ecc7
f216798d3c1687a282c7dbb055857bb3eb386f5aaea36c37a5cac9e737c11ea653563
3e937ac2a351dc3fae28ced2e82e7824c386e4918a839baa9025a7afa524e6102c103
000000000000000000000000000000000000000000000000000000000000000000000
0000000000000000000000000000000000000000000
P3 binding_factor: 15fe28f985bf28ad3deb1888f4e2795cd0d651a23b055257a4
2cb7fb2807a32c40d864540ce41757facee8bd0394cac614a6a29995a3cb2700

// Round two parameters
participant_list: 1,3

// Signer round two outputs
P1 sig_share: 6e997b6571c043ac7f22d09c216569da7d3824eb431c695f3d42e4e
049e962ed5b0e7edf18ed181f153973e954a24e339d8b4529467f413400
P3 sig_share: 962b26586f55d66deb5e4d1365d9df1b725871b6c2acac4239f6206
c4cfb335ce0332a9683d5c327eee642abd1c55fd5a931637fecd1a40800

sig: 20b7310c9c9e5bf2c24e3e752fd89a14452c0acb7bf6ad2692a366dddc0664a8
e437d99d5fdafa20d41e49088021dc41d8dfd34984f3abda0004c5a1bde0151a1a6b8
11db0863e49f6ef9095a106c915a27638054d96e496493c42a8759cc2dc460320b694
2668ae0847bda8a83251e63c00
~~~

## FROST(ristretto255, SHA-512)

~~~
// Configuration information
MAX_PARTICIPANTS: 3
MIN_PARTICIPANTS: 2
NUM_PARTICIPANTS: 2

// Group input parameters
group_secret_key: 8662bca8c2a073143e6623188a6f1f446298e1eef3c379392ca
aed06037b1402
group_public_key: fa631584cb6559b2251facf8d1478eb39c71c35c9a9f6b00d66
6e9fd022ddd29
message: 74657374
share_polynomial_randomness: 332ee11aac35ddead245cb0542fd3778d8f7fa6f
3fef538da54b74de058b8c50

// Signer input parameters
P1 participant_share: 2ab39bafea45e2fa2e190f144f5766ba1982950d87015c9
6efc0e28b0b87c407
P2 participant_share: ce037bb612eb50e11fccfa0f143fad30d16b492c1a3f3ef
3b2d7d7101493740d
P3 participant_share: 85806460202dad6f3ae2ee68fa2c15928855fd4aad7c205
076eecc951c9f2403

// Round one parameters
participant_list: 1,3

// Signer round one outputs
P1 hiding_nonce_randomness: 226f06e4c5280b907ce09ec4240d02531a34dba05
9d9b9b1152747f12d31a3d3
P1 binding_nonce_randomness: fd54f7fb9fa28a59b1002bfa057835f1d2caadd0
986a73c15451197c3f781bf0
P1 hiding_nonce: 1bb5161e272c6a577cd99ee20927564ab8ca8bd6cf3c1d8d907b
11991fd64c01
P1 binding_nonce: e75b2978ec80a328f23a6e89338600f0f77b7edf7dc02b9deea
b6244f1aa9e0c
P1 hiding_nonce_commitment: 68740443c09b6ab8940a387dc5195d89984106dc8
f6be68fbbbc768c2753ae17
P1 binding_nonce_commitment: 72d8d11fc55fad938a4eeaaa170e2558e083ae63
00141adce771659d39d8e278
P1 binding_factor_input: 9c245d5fc2e451c5c5a617cc6f2a20629fb317d9b1c1
915ab4bfa319d4ebf922c54dd1a5b3b754550c72734ac9255db8107a2b01f361754d9
f13f428c2f6de9e5e5aed7a723943b92b47d85e265e6365bd5cc252a05cfb059c376a
0982f6a64c63eec3273110dad0d0633783c3bd4294467d7558be7bdd8a4d11bec0c2b
cf08a0100000000000000000000000000000000000000000000000000000000000000
P1 binding_factor: 3c07bebf89da91f226618e939cb65d30432808efbbaa9e5bd3
0f9856117af808
P3 hiding_nonce_randomness: 0d2d5ef60cbfe595a47b345c0b8740c3af11e37ee
a2ab11700c9a07e210f0fee
P3 binding_nonce_randomness: 54596e1f1acd9f68d6ac7ce3946867dd5b2d7bd3
df53e562227fd6dbb7e49fd5
P3 hiding_nonce: 2cdb9087ca0fff654afd3d976e6ffebdb93888fde84e00b87913
267a86560805
P3 binding_nonce: 1dc5ba53b0fdf63610cdacb226aad7be3934eae5b444f9ce86d
e2dfb59fe3704
P3 hiding_nonce_commitment: 2e549c2df60b1352c89f0cc868dd3c6f19368696f
3ee4e176ded8a8804c3fa5d
P3 binding_nonce_commitment: b8750af0bba5ff7af719aeb09ba760016f55e26e
e4e389079b245183dff50917
P3 binding_factor_input: 9c245d5fc2e451c5c5a617cc6f2a20629fb317d9b1c1
915ab4bfa319d4ebf922c54dd1a5b3b754550c72734ac9255db8107a2b01f361754d9
f13f428c2f6de9e5e5aed7a723943b92b47d85e265e6365bd5cc252a05cfb059c376a
0982f6a64c63eec3273110dad0d0633783c3bd4294467d7558be7bdd8a4d11bec0c2b
cf08a0300000000000000000000000000000000000000000000000000000000000000
P3 binding_factor: c7699c1a0edae509aa6c192aede8a1f78b374c0021479a3c79
2a236e66637301

// Round two parameters
participant_list: 1,3

// Signer round two outputs
P1 sig_share: 33646bf4ee134562cfd09d33152fb6679c32d671c07c14f96b65f5d
aec36de01
P3 sig_share: f1beab3b8ce9e8dd6bee2d981422586974a94e24a22ce680b02451a
581671906

sig: 74f6deee7d7e14ae8a1d993e9280c06d9ad50217a23d5062e9daf0a5c9b1b80f
242317307bfd2d403bbfcbcb29510ed110dc249662a9fa791c8a46806e9ef707
~~~

## FROST(P-256, SHA-256)

~~~
// Configuration information
MAX_PARTICIPANTS: 3
MIN_PARTICIPANTS: 2
NUM_PARTICIPANTS: 2

// Group input parameters
group_secret_key: 1736f5a80b747a5a27d08458e8c5672909e0e47c0b8ed477d38
7e581198ad5db
group_public_key: 03f4ff4c12871603e81b12a47b1b40da905668dc6e29c9d2fe6
d8eb5fb1f869751
message: 74657374
share_polynomial_randomness: 7b2f307b74c0b213c0b56467be7a02980b51f5a4
24b3be9d79b6174cf2084a2e

// Signer input parameters
P1 participant_share: b9e0744694559b76b83d2135e96c93f5b5c5fd1814828f3
e2da0a240fab3b362
P2 participant_share: 5c89f2e61d36bc9248a9be12ea13c0c2a4c41b06765eab7
f93ff943ddf796b98
P3 participant_share: ff337184a617ddaed9165aefeabaed8f50a933a27f52664
5ee1850fdc0a2491f

// Round one parameters
participant_list: 1,3

// Signer round one outputs
P1 hiding_nonce_randomness: 3a9f89f95e391688f290312ef12727438fc1d5072
55582748bd7f0777e829659
P1 binding_nonce_randomness: 8df63a1f316ac41a524ef41cc2c2b087b6d20b5c
0ebf6cdd9c13fa5716f20cde
P1 hiding_nonce: 976e73aa6d1159e586f2d424b6d7497c07516dd6ff4cea3362e1
31e9b262317f
P1 binding_nonce: 8ce849c664eef3b38a5af38d9f9b5bcaac943c9ee26f17885b6
72fd8f7852f6b
P1 hiding_nonce_commitment: 021f61c7847ca029c161885f9b093ba376dc34c09
3b3e79902c9a8de420e9fa635
P1 binding_nonce_commitment: 03d2bc66eecc195619448f8e73f154a3529048be
91842b0d62e31a6608028fda13
P1 binding_factor_input: 350c8b523feea9bb35720e9fbe0405ed48d78caa4fb6
0869f34367e144c68bb01dcaba867c2749875ea0e4de577a03c9cfe37cacca2541732
271fa93e6df34e5000000000000000000000000000000000000000000000000000000
0000000001
P1 binding_factor: edd5e34e54fed2be85f5a919da8cbfaf16890bb2e3bf60cdc6
6d98c56c8de1a8
P3 hiding_nonce_randomness: 4b851f8c67325652fed86d75861f8cfbe2272a007
a13d69a640a836d4d9b3a55
P3 binding_nonce_randomness: 0d2af4268b13f16aee425b45c72004472eccc25c
971f0035aab1b8f2e8430958
P3 hiding_nonce: e63202f68bf33eaaa25a18bf43505d9b79107bc459804f31c5b0
ca9388c3a2a0
P3 binding_nonce: 72f61545bc887af28e48629a4c653c5e77f936f95c58442451e
3aad8164fbec7
P3 hiding_nonce_commitment: 02ec2b7af1b3784022054e2cf4fcd084263cd48d1
85f71b325fa52960b962b7c45
P3 binding_nonce_commitment: 03f4f625bb160a3ab8222ae72c4d2e0bcdeb0212
133f36ca191793dd5b15274f49
P3 binding_factor_input: 350c8b523feea9bb35720e9fbe0405ed48d78caa4fb6
0869f34367e144c68bb01dcaba867c2749875ea0e4de577a03c9cfe37cacca2541732
271fa93e6df34e5000000000000000000000000000000000000000000000000000000
0000000003
P3 binding_factor: cd21704a79782afbb77bc4e84042816bd679c4e5db378a0471
a8e84f60a6debe

// Round two parameters
participant_list: 1,3

// Signer round two outputs
P1 sig_share: b6d265bb02c7262b77dcf762059f3f2d23f1ef8c5707e88a0eff450
c665f96b8
P3 sig_share: 3d6b09f7696bc1553b29be3656a6289ee8c128a451cfee817cacab2
ee0b69ec3

sig: 02ef87df6d96ef031bdcae733cc2f9c068da51883a2de104d6f96acdec07f009
84f43d6fb26c32e780b306b5985c4567cc0cb31830a8d7d70b8babf03b4716357b
~~~

## FROST(secp256k1, SHA-256)

~~~
// Configuration information
MAX_PARTICIPANTS: 3
MIN_PARTICIPANTS: 2
NUM_PARTICIPANTS: 2

// Group input parameters
group_secret_key: f4329d087f45ab3ff9f1b30422c8267963162ef8d5d2458a9e9
91ac02257df96
group_public_key: 03d6bf91afdb5ac930d3208d6f85fecd7ee3a11ea54af064366
5e16601db4ca24b
message: 74657374
share_polynomial_randomness: ec72630e27dc7b7fe04de1a99bfd0f96d0e34fb4
da7f0d59eefa6351514a2056

// Signer input parameters
P1 participant_share: eeffb3f3d662c9ad8a2eb354c1b1f545eecb9beb9b97ce9
e716220c57b8dec4f
P2 participant_share: e9cccadf2d7fe81b1a6bb3a5609bc4127a8108de615d57b
2442b26cad4c3f908
P3 participant_share: e499e1ca849d0688aaa8b3f5ff8592df063675d12722e0c
616f42cd02dfa05c1

// Round one parameters
participant_list: 1,3

// Signer round one outputs
P1 hiding_nonce_randomness: 7c4d40afffa9a9cc6154133af34756146cefd3c69
65ae3931a069d98c6a6598f
P1 binding_nonce_randomness: 6e5be2429e917c0154e980cc26afcd355ff561c2
4cb7b273065a23ea8d9545da
P1 hiding_nonce: 564f417b9dfd8b418a25b6ded7625af4e4d491544b6b5aa3cb70
96cc6f39c50f
P1 binding_nonce: e3fe8cd0d0d7758fd75ddd8c4089e931ab13d0cba9bd7021d4c
2a310da54be3d
P1 hiding_nonce_commitment: 039e0442587c95d3ad6eb75e4ba2fe0c02b1e7fc6
c5e6fa94a5740bfaf152d3d16
P1 binding_nonce_commitment: 02cf0d6d13c798a5ee9ca64e3a3d5ed45e29e1a8
aed3b1e26562956f6633e7f134
P1 binding_factor_input: a645d8249457bbcac34fa7b740f66bcce08fc39506b8
bbf1a1c81092f6272eda6c7d7fb42a9a5ed84a4be302152da992c7a2d3e486a72fbe2
fe43da9459c1dca000000000000000000000000000000000000000000000000000000
0000000001
P1 binding_factor: 3c8ddb90e4ec052d7468f9ff223a07ab184391b0f8cb3e3dd6
241dd6d47b23d1
P3 hiding_nonce_randomness: 065f54b6d6e4581c89e622fc83eb97f926398b911
f60fc14a652fa0a298de0a6
P3 binding_nonce_randomness: bd2191fedc145fb64f80c5af87ca3a4c0d59f20a
70e277eb5e4d4f3fe9322308
P3 hiding_nonce: c47918eccdfa5070a7d89c34b3e64f98b28ba17144543be6cfec
a227f6cee5a2
P3 binding_nonce: e4d3ce30fc58660bc9f146a25b16bf72d64acabc7296834f072
0144951bb740b
P3 hiding_nonce_commitment: 03b23322cc3ab6fd5f53621af0ce3abe6c31f5542
3dcdefaeca4c907aab2f583ef
P3 binding_nonce_commitment: 036b2f3d3c615c5971d72003fe589b31d97f9d35
e4d3b9c4742528ecb05e88cbaf
P3 binding_factor_input: a645d8249457bbcac34fa7b740f66bcce08fc39506b8
bbf1a1c81092f6272eda6c7d7fb42a9a5ed84a4be302152da992c7a2d3e486a72fbe2
fe43da9459c1dca000000000000000000000000000000000000000000000000000000
0000000003
P3 binding_factor: 621845d4f6d7bd4b804aeccfaa75e935d01ba9e34832e75e04
8bd042f9a197f0

// Round two parameters
participant_list: 1,3

// Signer round two outputs
P1 sig_share: b3bbc339d9629906f2db5fb2a466f7c2604d686e098156f73bf6345
56c212259
P3 sig_share: 1af6c2ced3aec7f9715bb7715a2b22be719342189fa9259c28c13c5
91ae5c4af

sig: 02bf1ebd39f9e6d179bfddc42c4cfd018e0d4e0af55d1423ecad4142e2dc69c3
44ceb28608ad11610064371723fe921a80d1e0aa86a92a7c9364b770ae8706e708
~~~
