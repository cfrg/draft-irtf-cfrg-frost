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
The value of the contextString parameter is "FROST-ED25519-SHA512-v10".

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
  - H4(m): Implemented by computing H(contextString \|\| "msg" \|\| m).
  - H5(m): Implemented by computing H(contextString \|\| "com" \|\| m).


Normally H2 would also include a domain separator, but for backwards compatibility
with {{!RFC8032}}, it is omitted.

Signature verification is as specified in {{Section 5.1.7 of RFC8032}} with the
constraint that implementations MUST check the group equation [8][S]B = [8]R + [8][k]A'.
The alternative check [S]B = R + [k]A' is not safe or interoperable in practice.

## FROST(ristretto255, SHA-512) {#recommended-suite}

This ciphersuite uses ristretto255 for the Group and SHA-512 for the Hash function `H`.
The value of the contextString parameter is "FROST-RISTRETTO255-SHA512-v10".

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
  - H4(m): Implemented by computing H(contextString \|\| "msg" \|\| m).
  - H5(m): Implemented by computing H(contextString \|\| "com" \|\| m).

Signature verification is as specified in {{prime-order-verify}}.

## FROST(Ed448, SHAKE256)

This ciphersuite uses edwards448 for the Group and SHAKE256 for the Hash function `H`
meant to produce signatures indistinguishable from Ed448 as specified in {{!RFC8032}}.
The value of the contextString parameter is "FROST-ED448-SHAKE256-v10".

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
  - H4(m): Implemented by computing H(contextString \|\| "msg" \|\| m).
  - H5(m): Implemented by computing H(contextString \|\| "com" \|\| m).

Normally H2 would also include a domain separator, but for backwards compatibility
with {{!RFC8032}}, it is omitted.

Signature verification is as specified in {{Section 5.2.7 of RFC8032}} with the
constraint that implementations MUST check the group equation [4][S]B = [4]R + [4][k]A'.
The alternative check [S]B = R + [k]A' is not safe or interoperable in practice.

## FROST(P-256, SHA-256)

This ciphersuite uses P-256 for the Group and SHA-256 for the Hash function `H`.
The value of the contextString parameter is "FROST-P256-SHA256-v10".

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
  - H4(m): Implemented by computing H(contextString \|\| "msg" \|\| m).
  - H5(m): Implemented by computing H(contextString \|\| "com" \|\| m).

Signature verification is as specified in {{prime-order-verify}}.

## FROST(secp256k1, SHA-256)

This ciphersuite uses secp256k1 for the Group and SHA-256 for the Hash function `H`.
The value of the contextString parameter is "FROST-secp256k1-SHA256-v10".

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
  - H4(m): Implemented by computing H(contextString \|\| "msg" \|\| m).
  - H5(m): Implemented by computing H(contextString \|\| "com" \|\| m).

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
P1 hiding_nonce_randomness: 6c69be7a46a0e3be20833f864c77788bb05d6c239
8ceadb84dbafa9522520049
P1 binding_nonce_randomness: f6e164329c66be6fa75954dde46967171be80dda
fd1d1defe51f03f6e3e6876e
P1 hiding_nonce: 4e64f59e90a3b9cdce346fae68eb0e459532c8ca1ad59a566c3e
e2c67bf0100b
P1 binding_nonce: 470c660895c6db164ee6564120eec71023fa5297f09c663bb81
71646c5632d00
P1 hiding_nonce_commitment: f0ff219693d61f164ca785e03d6209ef94d57047c
fc5c14d2cab4eb70c5fb0f4
P1 binding_nonce_commitment: 71269d5f41d79e3d13059170875bf437c28369c6
7aa6ae7478faf1334550c8d0
P1 binding_factor_input: 736c1aac57730ec200b2e1518606c711d9ea10906582
8e5ff26e81eb0247093047543440063365d5442a86234a8c9808720b77e094ace1f0c
924183e30605b86dae87916da6a9544612f403ea4789735698142db05b44519ce717d
a7cee249174689aa30845e44d8f93d5993259112e5f17e293ece62de4a844f79ef1f4
61db00100000000000000000000000000000000000000000000000000000000000000
P1 binding_factor: 02e82a18a7de829a93e63114d56841e060affd3595c8079fe7
dea00eec053806
P3 hiding_nonce_randomness: a2de7b16419a23bf116e6b89f75264802063944d1
131ec7d9e789e01ab002aa1
P3 binding_nonce_randomness: 177cec6de656b2c53f53198e74fefcb387753b45
470ab373dc93a1adfbaafabf
P3 hiding_nonce: 6fc516495dbb364b807cdd0c2e5e3f58aa4914a53fed33cc3400
33979bb07304
P3 binding_nonce: 0837e770a88147d41ff39138ca23b35d6cf303a4f148294755e
de4b7e760d701
P3 hiding_nonce_commitment: a98ebfeab6684035cc51983f72e682837c70dd8a8
f6dfd52f116680ba35e9d54
P3 binding_nonce_commitment: bb6f0926361c9ef40a171bfcee67c3a693fc25a6
0e8a8d40d35f31829fda7799
P3 binding_factor_input: 736c1aac57730ec200b2e1518606c711d9ea10906582
8e5ff26e81eb0247093047543440063365d5442a86234a8c9808720b77e094ace1f0c
924183e30605b86dae87916da6a9544612f403ea4789735698142db05b44519ce717d
a7cee249174689aa30845e44d8f93d5993259112e5f17e293ece62de4a844f79ef1f4
61db00300000000000000000000000000000000000000000000000000000000000000
P3 binding_factor: f573b30ea1920f52dab3ec741430ce7b8838cd16ed0ff9b9d1
32e13e62c01601

// Round two parameters
participant_list: 1,3

// Signer round two outputs
P1 sig_share: 3f2eb12735e5b39da97e884a6caadf6bb83f1efcec709d6f66333d0
d67ebe707
P3 sig_share: 79e572b8632fbb928519dd2eff793de8784a56d582ae48c807d39b0
dc5b93509

sig: e31e69a4e10d5ca2307c4a0d12cd86e3fceee550e55cb5b3f47c7ad6dbb38884
cb3f2e837eb15cd858fb6dd68c2a3e3f318a74d16f1fe6376e06d91a2ca51d01
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
P1 hiding_nonce_randomness: 924ca0a20602aecf5b46a44191beae0f82662a934
5d8bba273e752d49cf09d38
P1 binding_nonce_randomness: 53cd669e849b4d2a357f122f5ba3b99242bde269
791ed1194a855e10befdaad3
P1 hiding_nonce: 06f2e15b05d29a50f0686a890259f4dcf66147a80809ed9e5092
6f5f173fe23a0627561efa003724dc270effc47a30bc4d80aba30725401d00
P1 binding_nonce: e0482e611c34f191d1c13a09bc8bbf4bda68db4de32aa790884
9b02ba912cfba46c805e2d8560ab9437e343e1dde6b481a2bae527e111b2c00
P1 hiding_nonce_commitment: 7034e3ad2c5641259d481fcc32b56b4552d3d0369
11dc456f948858bfca51c2c231d407222b9d6d997ff3c093309895c0ec510272b7cf0
bd00
P1 binding_nonce_commitment: 90d557d616fd4d495044fef2cd9da9ef7e962950
0888bc715d68702510f4757eb2eebe85493d2cc73c1d785b57984ee220da72fdedc35
7fc00
P1 binding_factor_input: 80c3dfd62df16cc677ad6772d130badcd6dbd9754fd1
939a3db6252646088570c91470beec2cf5e32dac40f5ab582cbd21f538f48a69ad053
ffac2ddbb2c73e2b503edb94c3e86c1b71d114dda9980d87e7ce96172719c6de68869
f9552edcf4a909bb2010822c236cff0a52afb5e85f897137f4d456aef79b8212fb9a6
c22e8ab92b5455a01423a2f158324749f1828384d9dc96169753c7f19b206f7fd0a55
fd2a85311170c5e4953de3d48894d4aa978e29df2332293ca97390068753aee1e4008
a99d699d3a56451caeaed1b54be56a47a84c277b228f000232e75b32610db0c366001
000000000000000000000000000000000000000000000000000000000000000000000
0000000000000000000000000000000000000000000
P1 binding_factor: d4f54f478b17d57cb62beced74b1e1d04124ecd955445645e9
37bda9d501b06f2c029495267759b7ddb5a127fff61e913467dc045bd2721200
P3 hiding_nonce_randomness: 59eb2ee60798a0df135361845963f0e4f16529158
e89c2e5144c6fe9bf407087
P3 binding_nonce_randomness: 70814edfac5db2ab76c7e216859bbd87e5e2c092
e903e82fb8b4dc920378056c
P3 hiding_nonce: 295c56447c070157e6bc3c83ed2afca194569e07d0ad27d28a40
dec2c4107c07d507db20da1be62ea6976b8e53ab5d26e225c663f2e7151100
P3 binding_nonce: b97303a6c5ab12b6ad310834361033a19d99dfdf93109da721d
a35c3abbc5f29df33b3402692bef9f005bb8ea00af5ba20cc688360fd883100
P3 hiding_nonce_commitment: ee8acb4b1c466d539ffac6d7a66b934c2ba929fd0
4f45398d18e7086953a7e064a1bd61cfcf04d7cb3f2efc71fac2769a445ba187fe0e9
5280
P3 binding_nonce_commitment: e81d75c6d11d14cf22387dc1e3f1734dc6c8cb77
44a0473c6af46b133a5f94a7f9fba511c5f95b1ac7ab6542ff98603c5b2e0fc0554bb
bd800
P3 binding_factor_input: 80c3dfd62df16cc677ad6772d130badcd6dbd9754fd1
939a3db6252646088570c91470beec2cf5e32dac40f5ab582cbd21f538f48a69ad053
ffac2ddbb2c73e2b503edb94c3e86c1b71d114dda9980d87e7ce96172719c6de68869
f9552edcf4a909bb2010822c236cff0a52afb5e85f897137f4d456aef79b8212fb9a6
c22e8ab92b5455a01423a2f158324749f1828384d9dc96169753c7f19b206f7fd0a55
fd2a85311170c5e4953de3d48894d4aa978e29df2332293ca97390068753aee1e4008
a99d699d3a56451caeaed1b54be56a47a84c277b228f000232e75b32610db0c366003
000000000000000000000000000000000000000000000000000000000000000000000
0000000000000000000000000000000000000000000
P3 binding_factor: 4525e6d697a2b8e5a373d051061f3ecb3f1cf2fb462fe6ee95
75c3e71e15412244667b5406ed76c39c99f4b24d5e88d564082e926f5db12400

// Round two parameters
participant_list: 1,3

// Signer round two outputs
P1 sig_share: 5b65641e27007ec71509c6af5cf8527eb01fee5b2b07d8beecf6646
eb7e7e27d85119b74f895b56ba7561834a1b0c42639b122160a0b620800
P3 sig_share: 821b7ac04d7c01d970b0b3ba4ae8f737a5bac934aed1600b1cad760
11c240629bce6a4671a1b6f572cec708ec161a72a5ca04e50eabdfc2500

sig: c7ad7ad9fcfeef9d1492361ba641400bd3a3c8335a83cdffbdd8867d2849bb44
19dcc3e594baa731081a1a00cd3dea9219a81ecba4646e9500dd80dede747c7fa086b
9796aa7e04ab655dab790d9d838ca08a4db6fd30be9a641f83fdc12b124c3d34289c2
62126c5195517166f4c85e2e00
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
P1 hiding_nonce_randomness: 0a016efd0abf8e556fd67288950bb7fc0843be63e
306c7264bc9d24d1d65e0ee
P1 binding_nonce_randomness: 35b6bab19e3e931e36c612ccc6b3c9d3a3479d27
04aac3324b79c7bb6665acfb
P1 hiding_nonce: de3e8f526dcb51a1b9b48cc284aeca27c385aa3ba1a92a0c8440
d51e1a1d2f00
P1 binding_nonce: fa8dca5ec7a05d5a7b782be847ba3dde1509de1dbcf0569fc98
0cff795db5404
P1 hiding_nonce_commitment: 3677297a5df660bf63bb8fcae79b7f98cf4f2e99f
61bc762de9795cacd1cba62
P1 binding_nonce_commitment: 142aece8aa8b16766664d8aaa5a5e709404bb844
3309ef1ea9ad9254794a1f09
P1 binding_factor_input: c70ac0b3effa113b8f4d8a6b1393ef7f0910862d143f
de83e410db94f3818295ff49ed5aed0e57b2712f2ce0f9166f1ffdce282786c7ee8c2
db2df295c61dc5fd0f93a769d09d44352c4e709c2e239fc34a1b89db44cb241060228
5ffd70f3fa0a62dd70cfdb369ac0a7efc587f6f671a88412b2570280da24bd36f8ffd
a6d280100000000000000000000000000000000000000000000000000000000000000
P1 binding_factor: dbaa0ae3c5663816cdc646281be46b0b09eca6a1ecf7781f29
475be27d30fd08
P3 hiding_nonce_randomness: ac4e65529397de3a868a902e9040e38b26547c18b
7267fa1d1bbfe4ed14d6b5f
P3 binding_nonce_randomness: 74213c820b7266c4990a0758f4c520685375cb98
822499406654bdb1a426582e
P3 hiding_nonce: e07061a9ab6735de9a75b0c64f086c5b999894611d0cdc03f85c
4e87c8aae602
P3 binding_nonce: 38b17578e8e6ad4077071ce6b0bf9cb85ac35fee7868dcb6d9b
fa97f0e153e0e
P3 hiding_nonce_commitment: f8d758ad9373754c1d2bca9c38478e4eb857aa032
836ade6eb0726f5e1d08037
P3 binding_nonce_commitment: 529823e80220849c195072a26acca88f65639d41
81927bb7fcd96e43d9a34649
P3 binding_factor_input: c70ac0b3effa113b8f4d8a6b1393ef7f0910862d143f
de83e410db94f3818295ff49ed5aed0e57b2712f2ce0f9166f1ffdce282786c7ee8c2
db2df295c61dc5fd0f93a769d09d44352c4e709c2e239fc34a1b89db44cb241060228
5ffd70f3fa0a62dd70cfdb369ac0a7efc587f6f671a88412b2570280da24bd36f8ffd
a6d280300000000000000000000000000000000000000000000000000000000000000
P3 binding_factor: aa076fec41410f6c0667e47443fcd1ed828854d84b19d1d086
24d084720c7d05

// Round two parameters
participant_list: 1,3

// Signer round two outputs
P1 sig_share: a5f046916a6a111672111e47f9825586e1188da8a0f3b7c61f2b6b4
32c636e07
P3 sig_share: 4c175c7e43bd197980c2021774036eb288f54179f079fbf21b7d2f9
f52846401

sig: 94b11def3f919503c3544452ad2a59f198f64cc323bd758bb1c65b42032a7473
f107a30fae272b8ff2d3205e6d86c3386a0ecf21916db3b93ba89ae27ee7d208
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
P1 hiding_nonce_randomness: 3029ae05a266703f618e60c26653f6b8f35a759ec
2adecf8b7d9e1719375494e
P1 binding_nonce_randomness: 86755fd9be109ff0549833931080ac344b0d775a
029fca0329f8ce732060f81e
P1 hiding_nonce: 9aa66350b0f72b27ce4668323b4280cd49709177ed8373977c22
a75546c9995d
P1 binding_nonce: bd8b05d7fd0ff5a5ed65b1f105478f7718a981741fa8fa9b55a
c6d3c8fc59a05
P1 hiding_nonce_commitment: 03071549b356988df0f7187585e2d82d6f916700c
fdd49634d0c27965139fd53ec
P1 binding_nonce_commitment: 02151f45451b719bf68f6c609967ebea3c78c9ec
e4c04a564a0c50d22f0f534112
P1 binding_factor_input: 47d0b1c45754dd58dc369bc4c1a9b24ffbb67ceb6d6e
25c302e9875202f7d2b4755d9beaba0a02b01315bd42fa11590d5a4d531d1f7f81c5f
c70a82ecada72e9000000000000000000000000000000000000000000000000000000
0000000001
P1 binding_factor: 0e9709d66649a0a245f28666bd01c863a6a647f213fd49eeaa
cfeca15402ddf4
P3 hiding_nonce_randomness: 2741900f778d51f4431644a62a69f1623d7569ecf
2d628d60cb28e27db949161
P3 binding_nonce_randomness: a62404370cb2a2e0aebef27ec72c1433a627dfcc
5f0cdf5ba4799fc326a66a3f
P3 hiding_nonce: 4c1aec8e84c496b80af98415fada2e6a4b1f902d4bc6c9682699
b8aeffd97419
P3 binding_nonce: eeaf5ef7af01e55050fb8acafc9c9306ef1cc13214677ba33e7
bc51e8677e892
P3 hiding_nonce_commitment: 0351cd636672cac59d384498dd9db2b72ea8e701a
702867c17e3ecf675d9a9fc91
P3 binding_nonce_commitment: 032bddd1ab4bfda79c707742f0e314ff2be95940
58ba590613ba9840886bab1a59
P3 binding_factor_input: 47d0b1c45754dd58dc369bc4c1a9b24ffbb67ceb6d6e
25c302e9875202f7d2b4755d9beaba0a02b01315bd42fa11590d5a4d531d1f7f81c5f
c70a82ecada72e9000000000000000000000000000000000000000000000000000000
0000000003
P3 binding_factor: 0b5c759331915b25c5eb5307617e01aa99bc5c89a403d9c6b5
9949045a4c0a77

// Round two parameters
participant_list: 1,3

// Signer round two outputs
P1 sig_share: ec5b8ab47d55903698492a07bb322ab6e7d3cf32581dcedf43c4fa1
8b46f3e10
P3 sig_share: c97da3580560e88725a8e393d46fee18ecd2e00148e5e303d4a510f
ae9c11da5

sig: 036b3eba585ff5d40df29893fb6f60572803aef97800cfaaaa5cf0f0f19d8237
f7b5d92e0d82b678bcbdf20d9b8fa218d017bfb485f9ec135e24b04050a1cd3664
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
P1 hiding_nonce_randomness: 753a4f3d424de828c2604f54a807677e4383a184b
f373da9855af385e9014693
P1 binding_nonce_randomness: 4f4b423493e7e676d30630c0b165cf6ea428bd43
1af382377981a7f3971ba3f0
P1 hiding_nonce: 36d5c4185c40b02b5e4673e2531a10e6ff9883840a68ec08dbeb
896467e21355
P1 binding_nonce: 7b3f573ca0a28f9f94522be4748df0ed04de8a83085aff4be7b
01aa53fb6ac1b
P1 hiding_nonce_commitment: 029ed3b6b8c3f7c1bca427160579ea1cdf47671c7
76ed1933fb617c7d8ebd018cd
P1 binding_nonce_commitment: 0217c99463f8ced8a2f2927a85d9a5fcc893bcf9
a6dc0507418e6f511feea0964d
P1 binding_factor_input: 8263cf41514645b3d57a9738502a0522c8d7b410ec42
b6ba8cca0830faacfa01cabeb24393904d4051842b28fd09f3f53dd6812c1331a225d
c9c9c6f872fe734000000000000000000000000000000000000000000000000000000
0000000001
P1 binding_factor: f995eeab0b6c02673f1e5e338652eac32729d9e827518f8350
934261f7f8a118
P3 hiding_nonce_randomness: 94b70f287aa5c9961a012e00c46f384cf7cc4b385
f7d6f093e53c60117aae9a2
P3 binding_nonce_randomness: a6b5ebff4fe4539535c33bcc267bb5f25c40e300
8bf118ba8a97a12e131d0e8a
P3 hiding_nonce: ba4f8b8e587b2c9fc61a6156885f0bc67654b5e068c9e7749f75
c09a98f17c13
P3 binding_nonce: 316de06639051ac7869e5ac4458eda1fef90ce93fa3c490556c
4192e4fa550d0
P3 hiding_nonce_commitment: 037d38246f1ac0d713a79956723e7766861ce624e
7e3bfc98c786d5e20c6ae232a
P3 binding_nonce_commitment: 03342d96ef52ad1f95423f32ef17805595393268
f606c3a6d179e4f99910a41dfe
P3 binding_factor_input: 8263cf41514645b3d57a9738502a0522c8d7b410ec42
b6ba8cca0830faacfa01cabeb24393904d4051842b28fd09f3f53dd6812c1331a225d
c9c9c6f872fe734000000000000000000000000000000000000000000000000000000
0000000003
P3 binding_factor: 73dce3f4ade1d8a357bb4b219840da9ef6f99551cafcfe174e
5d93f1994f5891

// Round two parameters
participant_list: 1,3

// Signer round two outputs
P1 sig_share: f9ee00d5ac0c746b751dde99f71d86f8f0300a81bd0336ca6649ef5
97239e13f
P3 sig_share: 61048ca334ac6a6cb59d6b3ea2b25b7098e204adc09e2f88b024531
b081d1d6f

sig: 023cf76388f92d403aa937af2e3cb3e7a2350e40400c16a282e330af2c60eeb8
5a5af28d78e0b8ded82abb49d899cfe26ace633248ce58c617569be3e7aa20bd6d
~~~
