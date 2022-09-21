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
require cooperation among a threshold number of signers each holding a share
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
from linear in the number of signers to constant, this draft does not specify that optimization
due to the malleability that this optimization introduces, as shown in {{StrongerSec22}}.
Specifically, this optimization removes the guarantee that the set of signers that started
round one of the protocol is the same set of signers that produced the signature output by
round two.

Key generation for FROST signing is out of scope for this document. However, for completeness,
key generation with a trusted dealer is specified in {{dep-dealer}}.

## Change Log

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
- Rename THRESHOLD_LIMIT to MIN_SIGNERS (#192)
- Use non-contiguous signers for the test vectors (#187)
- Add more reasoning why the coordinator MUST abort (#183)
- Add a function to generate nonces (#182)
- Add MUST that all participants have the same view of VSS commitment (#174)
- Use THRESHOLD_LIMIT instead of t and MAX_SIGNERS instead of n (#171)
- Specify what the dealer is trusted to do (#166)
- Clarify types of NUM_SIGNERS and THRESHOLD_LIMIT (#165)
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
We denote equality comparison as `==` and assignment of values by `=`.

We now detail a number of member functions that can be invoked on `G`.

- Order(): Outputs the order of `G` (i.e. `p`).
- Identity(): Outputs the identity `Element` of the group (i.e. `I`).
- RandomScalar(): Outputs a random `Scalar` element in GF(p), i.e., a random scalar in \[0, p - 1\].
- ScalarMult(A, k): Output the scalar multiplication between Element `A` and Scalar `k`.
- ScalarBaseMult(k): Output the scalar multiplication between Scalar `k` and the group generator `B`.
- SerializeElement(A): Maps an `Element` `A` to a unique byte array `buf` of fixed length `Ne`.
- DeserializeElement(buf): Attempts to map a byte array `buf` to an `Element` `A`,
  and fails if the input is not a valid byte representation of an element of
  the group. This function can raise a DeserializeError if deserialization fails
  or `A` is the identity element of the group; see {{ciphersuites}} for group-specific
  input validation steps.
- SerializeScalar(s): Maps a Scalar `s` to a unique byte array `buf` of fixed length `Ns`.
- DeserializeScalar(buf): Attempts to map a byte array `buf` to a `Scalar` `s`.
  This function can raise a DeserializeError if deserialization fails; see
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
and with the secret key as input to a domain-separated hash function built
from the ciphersuite hash function `H`. This domain-separated hash function
is denoted `H3`. This function always samples 32 bytes of fresh randomness
to ensure that the probability of nonce reuse is at most 2<sup>-128</sup>
as long as no more than 2<sup>64</sup> signatures are computed by a given
signer.

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
during the FROST protocol. The following function encodes a list of signer
commitments into a bytestring for use in the FROST protocol.

~~~
  Inputs:
  - commitment_list = [(i, hiding_nonce_commitment_i, binding_nonce_commitment_i), ...],
    a list of commitments issued by each signer, where each element in the list
    indicates the signer identifier i and their two commitment Element values
    (hiding_nonce_commitment_i, binding_nonce_commitment_i). This list MUST be sorted
    in ascending order by signer identifier.

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

The following function is used to extract signer identifiers from a commitment
list.

~~~
  Inputs:
  - commitment_list = [(i, hiding_nonce_commitment_i, binding_nonce_commitment_i), ...],
    a list of commitments issued by each signer, where each element in the list
    indicates the signer identifier i and their two commitment Element values
    (hiding_nonce_commitment_i, binding_nonce_commitment_i). This list MUST be sorted
    in ascending order by signer identifier.

  Outputs: A list of signer participant identifiers

def signers_from_commitment_list(commitment_list):
  identifiers = []
  for (identifier, _, _) in commitment_list:
    identifiers.append(identifier)
  return identifiers
~~~

The following function is used to extract a binding factor from a list of binding factors.

~~~
  Inputs:
  - binding_factor_list = [(i, binding_factor), ...],
    a list of binding factors for each signer, where each element in the list
    indicates the signer identifier i and their binding factor. This list MUST be sorted
    in ascending order by signer identifier.
  - identifier, signer identifier, a Scalar.

  Outputs: A Scalar value.

  Errors: "invalid signer", when the designated signer is not known

def binding_factor_for_signer(binding_factor_list, identifier):
  for (i, binding_factor) in binding_factor_list:
    if identifier == i:
      return binding_factor
  raise "invalid signer"
~~~

## Binding Factors Computation {#dep-binding-factor}

This section describes the subroutine for computing binding factors based
on the signer commitment list and message to be signed.

~~~
  Inputs:
  - commitment_list = [(i, hiding_nonce_commitment_i, binding_nonce_commitment_i), ...],
    a list of commitments issued by each signer, where each element in the list
    indicates the signer identifier i and their two commitment Element values
    (hiding_nonce_commitment_i, binding_nonce_commitment_i). This list MUST be sorted
    in ascending order by signer identifier.
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
    of commitments issued by each signer, where each element in the list
    indicates the signer identifier i and their two commitment Element values
    (hiding_nonce_commitment_i, binding_nonce_commitment_i). This list MUST be
    sorted in ascending order by signer identifier.
  - binding_factor_list = [(i, binding_factor), ...],
    a list of (identifier, Scalar) tuples representing the binding factor Scalar
    for the given identifier. This list MUST be sorted in ascending order by identifier.

  Outputs: An Element in G representing the group commitment

  def compute_group_commitment(commitment_list, binding_factor_list):
    group_commitment = G.Identity()
    for (identifier, hiding_nonce_commitment, binding_nonce_commitment) in commitment_list:
      binding_factor = binding_factor_for_signer(binding_factors, identifier)
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
run with a selection of `NUM_SIGNERS` signer participants and a Coordinator.
`NUM_SIGNERS` is a positive integer at least `MIN_SIGNERS` but no larger than
`MAX_SIGNERS`, where `MIN_SIGNERS < MAX_SIGNERS`, `MIN_SIGNERS` is a positive
integer and `MAX_SIGNERS` is a positive integer less than the group order.
A signer participant, or signer, is an entity that is trusted to hold and
use a signing key share. The Coordinator is an entity with the following responsibilities:

1. Determining which signers will participate (at least MIN_SIGNERS in number);
2. Coordinating rounds (receiving and forwarding inputs among signers); and
3. Aggregating signature shares output by each signer, and publishing the resulting signature.

FROST assumes that all participants, including the Coordinator and the set of signers,
are chosen externally to the protocol. Note that it is possible to deploy the protocol
without a distinguished Coordinator; see {{no-coordinator}} for more information.

FROST produces signatures that are indistinguishable from those produced with a single
signer using a signing key `s` with corresponding public key `PK`, where `s` is a Scalar
value and `PK = G.ScalarMultBase(s)`. As a threshold signing protocol, the group signing
key `s` is secret-shared amongst each signer and used to produce signatures. In particular,
FROST assumes each signer is configured with the following information:

- An identifier, which is a Scalar value denoted `i` in the range `[1, MAX_SIGNERS]`
  and MUST be distinct from the identifier of every other signer.
- A signing key share `sk_i`, which is a Scalar value representing the i-th secret share
  of the group signing key `s`. The public key corresponding to this signing key share
  is `PK_i = G.ScalarMultBase(sk_i)`.

Each signer participant, including the Coordinator, is additionally configured
with common group information, denoted "group info," which consists of the following
information:

- Group public key, which is an `Element` in `G` denoted `PK`.
- Public keys `PK_i` for each signer, which are `Element` values in `G` denoted `PK_i`
  for each `i` in `[1, MAX_SIGNERS]`.

This document does not specify how this information, including the signing key shares,
are configured and distributed to signers. In general, two possible configuration
mechanisms are possible: one that requires a single, trusted dealer, and the other
which requires performing a distributed key generation protocol. We highlight
key generation mechanism by a trusted dealer in {{dep-dealer}} for reference.

The signing variant of FROST in this document requires signers to perform two network rounds:
1) generating and publishing commitments, and 2) signature share generation and
publication. The first round serves for each signer to issue a commitment to
a nonce. The second round receives commitments for all signers as well as the message,
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
            |    signer commitment   |                 |
            |<-----------------------+                 |
            |          ...                             |
            |    signer commitment              (commit state) ==\
            |<-----------------------------------------+         |
                                                                 |
      == Round 2 (Signature Share Generation) ==                 |
            |                                                    |
            |     signer input       |                 |         |
            +------------------------>                 |         |
            |     signature share    |                 |         |
            |<-----------------------+                 |         |
            |          ...                             |         |
            |     signer input                         |         |
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
are described in {{frost-round-two}}. Note that each signer persists some state between
both rounds, and this state is deleted as described in {{frost-round-two}}. The final
Aggregation step is described in {{frost-aggregation}}.

FROST assumes that all inputs to each round, especially those of which are received
over the network, are validated before use. In particular, this means that any value
of type Element or Scalar is deserialized using DeserializeElement and DeserializeScalar,
respectively, as these functions perform the necessary input validation steps.

FROST assumes reliable message delivery between the Coordinator and signers in
order for the protocol to complete. An attacker masquerading as another signer
will result only in an invalid signature; see {{sec-considerations}}. However, in order
to identify any signer which has misbehaved (resulting in the protocol aborting)
to take actions such as excluding them from future signing operations, we assume that
the network channel is additionally authenticated; confidentiality is not required.

## Round One - Commitment {#frost-round-one}

Round one involves each signer generating nonces and their corresponding public commitments.
A nonce is a pair of Scalar values, and a commitment is a pair of Element values. Each signer's
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

The outputs `nonce` and `comm` from signer `P_i` should both be stored locally and
kept for use in the second round. The `nonce` value is secret and MUST NOT be shared, whereas
the public output `comm` is sent to the Coordinator. The nonce values produced by this
function MUST NOT be reused in more than one invocation of FROST, and it MUST be generated
from a source of secure randomness.

<!-- The Coordinator must not get confused about which commitments come from which signers, do we need to say more about how this is done? -->

## Round Two - Signature Share Generation {#frost-round-two}

In round two, the Coordinator is responsible for sending the message to be signed, and
for choosing which signers will participate (of number at least MIN_SIGNERS). Signers
additionally require locally held data; specifically, their private key and the
nonces corresponding to their commitment issued in round one.

The Coordinator begins by sending each signer the message to be signed along with the
set of signing commitments for all signers in the participant list. Each signer
MUST validate the inputs before processing the Coordinator's request. In particular,
the Signer MUST validate commitment_list, deserializing each group Element in the
list using DeserializeElement from {{dep-pog}}. If deserialization fails, the Signer
MUST abort the protocol. Moreover, each signer MUST ensure that their identifier as
well as their commitment as from the first round appears in commitment_list.
Applications which require that signers not process arbitrary
input messages are also required to also perform relevant application-layer input
validation checks; see {{message-validation}} for more details.

Upon receipt and successful input validation, each Signer then runs the following
procedure to produce its own signature share.

~~~
  Inputs:
  - identifier, Identifier i of the signer. Note identifier will never equal 0.
  - sk_i, Signer secret key share, a Scalar.
  - group_public_key, public key corresponding to the group signing key,
    an Element in G.
  - nonce_i, pair of Scalar values (hiding_nonce, binding_nonce) generated in
    round one.
  - msg, the message to be signed (sent by the Coordinator).
  - commitment_list =
      [(j, hiding_nonce_commitment_j, binding_nonce_commitment_j), ...], a
    list of commitments issued in Round 1 by each signer and sent by the Coordinator.
    Each element in the list indicates the signer identifier j and their two commitment
    Element values (hiding_nonce_commitment_j, binding_nonce_commitment_j).
    This list MUST be sorted in ascending order by signer identifier.

  Outputs: a Scalar value representing the signature share

  def sign(identifier, sk_i, group_public_key, nonce_i, msg, commitment_list):
    # Compute the binding factor(s)
    binding_factor_list = compute_binding_factors(commitment_list, msg)
    binding_factor = binding_factor_for_signer(binding_factor_list, identifier)

    # Compute the group commitment
    group_commitment = compute_group_commitment(commitment_list, binding_factor_list)

    # Compute Lagrange coefficient
    signer_list = signers_from_commitment_list(commitment_list)
    lambda_i = derive_lagrange_coefficient(identifier, signer_list)

    # Compute the per-message challenge
    challenge = compute_challenge(group_commitment, group_public_key, msg)

    # Compute the signature share
    (hiding_nonce, binding_nonce) = nonce_i
    sig_share = hiding_nonce + (binding_nonce * binding_factor) + (lambda_i * sk_i * challenge)

    return sig_share
~~~

The output of this procedure is a signature share. Each signer then sends
these shares back to the Coordinator. Each signer MUST delete the nonce and
corresponding commitment after this round completes, and MUST use the nonce
to generate at most one signature share.

Note that the `lambda_i` value derived during this procedure does not change
across FROST signing operations for the same signing group. As such, signers
can compute it once and store it for reuse across signing sessions.

Upon receipt from each Signer, the Coordinator MUST validate the input
signature share using DeserializeElement. If validation fails, the Coordinator MUST abort
the protocol. If validation succeeds, the Coordinator then verifies the set of
signature shares using the following procedure.

## Signature Share Verification and Aggregation {#frost-aggregation}

After signers perform round two and send their signature shares to the Coordinator,
the Coordinator verifies each signature share for correctness. In particular,
for each signer, the Coordinator uses commitment pairs generated during round
one and the signature share generated during round two, along with other group
parameters, to check that the signature share is valid using the following procedure.

~~~
  Inputs:
  - identifier, Identifier i of the signer. Note: identifier MUST never equal 0.
  - PK_i, the public key for the ith signer, where PK_i = G.ScalarBaseMult(sk_i),
    an Element in G
  - comm_i, pair of Element values in G (hiding_nonce_commitment, binding_nonce_commitment)
    generated in round one from the ith signer.
  - sig_share_i, a Scalar value indicating the signature share as produced in
    round two from the ith signer.
  - commitment_list =
      [(j, hiding_nonce_commitment_j, binding_nonce_commitment_j), ...], a
    list of commitments issued in Round 1 by each signer, where each element
    in the list indicates the signer identifier j and their two commitment
    Element values (hiding_nonce_commitment_j, binding_nonce_commitment_j).
    This list MUST be sorted in ascending order by signer identifier.
  - group_public_key, public key corresponding to the group signing key,
    an Element in G.
  - msg, the message to be signed.

  Outputs: True if the signature share is valid, and False otherwise.

  def verify_signature_share(identifier, PK_i, comm_i, sig_share_i, commitment_list,
                             group_public_key, msg):
    # Compute the binding factors
    binding_factor_list = compute_binding_factors(commitment_list, msg)
    binding_factor = binding_factor_for_signer(binding_factor_list, identifier)

    # Compute the group commitment
    group_commitment = compute_group_commitment(commitment_list, binding_factor_list)

    # Compute the commitment share
    (hiding_nonce_commitment, binding_nonce_commitment) = comm_i
    comm_share = hiding_nonce_commitment + G.ScalarMult(binding_nonce_commitment, binding_factor)

    # Compute the challenge
    challenge = compute_challenge(group_commitment, group_public_key, msg)

    # Compute Lagrange coefficient
    signer_list = signers_from_commitment_list(commitment_list)
    lambda_i = derive_lagrange_coefficient(identifier, signer_list)

    # Compute relation values
    l = G.ScalarBaseMult(sig_share_i)
    r = comm_share + G.ScalarMult(PK_i, challenge * lambda_i)

    return l == r
~~~

If any signature share fails to verify, i.e., if verify_signature_share returns False for
any signer share, the Coordinator MUST abort the protocol for correctness reasons
(this is true regardless of the size or makeup of the signing set selected by
the Coordinator).
Excluding one signer means that their nonce will not be included in the joint response `z`
and consequently the output signature will not verify. This is because the
group commitment will be with respect to a different signing set than the
the aggregated response.

Otherwise, if all shares from signers that participated in Rounds 1 and 2 are valid, the Coordinator
performs the `aggregate` operation and publishes the resulting signature.

~~~
  Inputs:
  - group_commitment, the group commitment returned by compute_group_commitment,
    an Element in G.
  - sig_shares, a set of signature shares z_i, Scalar values, for each signer,
    of length NUM_SIGNERS, where MIN_SIGNERS <= NUM_SIGNERS <= MAX_SIGNERS.

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
signer.

## FROST(Ed25519, SHA-512)

This ciphersuite uses edwards25519 for the Group and SHA-512 for the Hash function `H`
meant to produce signatures indistinguishable from Ed25519 as specified in {{!RFC8032}}.
The value of the contextString parameter is "FROST-ED25519-SHA512-v8".

- Group: edwards25519 {{!RFC8032}}
  - Order(): Return 2^252 + 27742317777372353535851937790883648493 (see {{?RFC7748}})
  - Identity(): As defined in {{RFC7748}}.
  - RandomScalar(): Implemented by returning a uniformly random Scalar in the range
    \[0, `G.Order()` - 1\]. Refer to {{random-scalar}} for implementation guidance.
  - SerializeElement(A): Implemented as specified in {{!RFC8032, Section 5.1.2}}.
  - DeserializeElement(buf): Implemented as specified in {{!RFC8032, Section 5.1.3}}.
    Additionally, this function validates that the resulting element is not the group
    identity element and is in the prime-order subgroup. The latter check can
    be implemented by multiplying the resulting point by the order of the group and
    checking that the result is the identity element.
  - SerializeScalar(s): Implemented by outputting the little-endian 32-byte encoding of
    the Scalar value.
  - DeserializeScalar(buf): Implemented by attempting to deserialize a Scalar from a
    little-endian 32-byte string. This function can fail if the input does not
    represent a Scalar in the range \[0, `G.Order()` - 1\].

- Hash (`H`): SHA-512, and Nh = 64.
  - H1(m): Implemented by computing H(contextString \|\| "rho" \|\| m), interpreting the 64-byte digest
    as a little-endian integer, and reducing the resulting integer modulo
    L = 2^252+27742317777372353535851937790883648493.
  - H2(m): Implemented by computing H(m), interpreting the 64-byte digest
    as a little-endian integer, and reducing the resulting integer modulo
    L = 2^252+27742317777372353535851937790883648493.
  - H3(m): Implemented by computing H(contextString \|\| "nonce" \|\| m), interpreting the 64-byte digest
    as a little-endian integer, and reducing the resulting integer modulo
    L = 2^252+27742317777372353535851937790883648493.
  - H4(m): Implemented by computing H(contextString \|\| "msg" \|\| m).
  - H5(m): Implemented by computing H(contextString \|\| "com" \|\| m).


Normally H2 would also include a domain separator, but for backwards compatibility
with {{!RFC8032}}, it is omitted.

Signature verification is as specified in {{Section 5.1.7 of RFC8032}} with the
constraint that implementations MUST check the group equation [8][S]B = [8]R + [8][k]A'.
The alternative check [S]B = R + [k]A' is not safe or interoperable in practice.

## FROST(ristretto255, SHA-512) {#recommended-suite}

This ciphersuite uses ristretto255 for the Group and SHA-512 for the Hash function `H`.
The value of the contextString parameter is "FROST-RISTRETTO255-SHA512-v8".

- Group: ristretto255 {{!RISTRETTO=I-D.irtf-cfrg-ristretto255-decaf448}}
  - Order(): Return 2^252 + 27742317777372353535851937790883648493 (see {{RISTRETTO}})
  - Identity(): As defined in {{RISTRETTO}}.
  - RandomScalar(): Implemented by returning a uniformly random Scalar in the range
    \[0, `G.Order()` - 1\]. Refer to {{random-scalar}} for implementation guidance.
  - SerializeElement(A): Implemented using the 'Encode' function from {{!RISTRETTO}}.
  - DeserializeElement(buf): Implemented using the 'Decode' function from {{!RISTRETTO}}.
    Additionally, this function validates that the resulting element is not the group
    identity element.
  - SerializeScalar(s): Implemented by outputting the little-endian 32-byte encoding of
    the Scalar value.
  - DeserializeScalar(buf): Implemented by attempting to deserialize a Scalar from a
    little-endian 32-byte string. This function can fail if the input does not
    represent a Scalar in the range \[0, `G.Order()` - 1\].

- Hash (`H`): SHA-512, and Nh = 64.
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
The value of the contextString parameter is "FROST-ED448-SHAKE256-v8".

- Group: edwards448 {{!RFC8032}}
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

- Hash (`H`): SHAKE256, and Nh = 114.
  - H1(m): Implemented by computing H(contextString \|\| "rho" \|\| m), interpreting the
    114-byte digest as a little-endian integer, and reducing the resulting integer modulo
    L = 2^446 - 13818066809895115352007386748515426880336692474882178609894547503885.
  - H2(m): Implemented by computing H("SigEd448" \|\| 0 \|\| 0 \|\| m), interpreting
    the 114-byte digest as a little-endian integer, and reducing the resulting integer
    modulo L = 2^446 - 13818066809895115352007386748515426880336692474882178609894547503885.
  - H3(m): Implemented by computing H(contextString \|\| "nonce" \|\| m), interpreting the
    114-byte digest as a little-endian integer, and reducing the resulting integer modulo
    L = 2^446 - 13818066809895115352007386748515426880336692474882178609894547503885.
  - H4(m): Implemented by computing H(contextString \|\| "msg" \|\| m).
  - H5(m): Implemented by computing H(contextString \|\| "com" \|\| m).

Normally H2 would also include a domain separator, but for backwards compatibility
with {{!RFC8032}}, it is omitted.

Signature verification is as specified in {{Section 5.2.7 of RFC8032}} with the
constraint that implementations MUST check the group equation [4][S]B = [4]R + [4][k]A'.
The alternative check [S]B = R + [k]A' is not safe or interoperable in practice.

## FROST(P-256, SHA-256)

This ciphersuite uses P-256 for the Group and SHA-256 for the Hash function `H`.
The value of the contextString parameter is "FROST-P256-SHA256-v8".

- Group: P-256 (secp256r1) {{x9.62}}
  - Order(): Return 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
  - Identity(): As defined in {{x9.62}}.
  - RandomScalar(): Implemented by returning a uniformly random Scalar in the range
    \[0, `G.Order()` - 1\]. Refer to {{random-scalar}} for implementation guidance.
  - SerializeElement(A): Implemented using the compressed Elliptic-Curve-Point-to-Octet-String
    method according to {{SEC1}}.
  - DeserializeElement(buf): Implemented by attempting to deserialize a public key using
    the compressed Octet-String-to-Elliptic-Curve-Point method according to {{SEC1}},
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

- Hash (`H`): SHA-256, and Nh = 32.
  - H1(m): Implemented using hash_to_field from {{!HASH-TO-CURVE=I-D.irtf-cfrg-hash-to-curve, Section 5.3}}
    using L = 48, `expand_message_xmd` with SHA-256, DST = contextString || "rho", and
    prime modulus equal to `Order()`.
  - H2(m): Implemented using hash_to_field from {{!HASH-TO-CURVE, Section 5.3}}
    using L = 48, `expand_message_xmd` with SHA-256, DST = contextString || "chal", and
    prime modulus equal to `Order()`.
  - H3(m): Implemented using hash_to_field from {{!HASH-TO-CURVE, Section 5.3}}
    using L = 48, `expand_message_xmd` with SHA-256, DST = contextString || "nonce", and
    prime modulus equal to `Order()`.
  - H4(m): Implemented by computing H(contextString \|\| "msg" \|\| m).
  - H5(m): Implemented by computing H(contextString \|\| "com" \|\| m).

Signature verification is as specified in {{prime-order-verify}}.

## FROST(secp256k1, SHA-256)

This ciphersuite uses secp256k1 for the Group and SHA-256 for the Hash function `H`.
The value of the contextString parameter is "FROST-secp256k1-SHA256-v8".

- Group: secp256k1 {{SEC2}}
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

- Hash (`H`): SHA-256, and Nh = 32.
  - H1(m): Implemented using hash_to_field from {{!HASH-TO-CURVE=I-D.irtf-cfrg-hash-to-curve, Section 5.3}}
    using L = 48, `expand_message_xmd` with SHA-256, DST = contextString || "rho", and
    prime modulus equal to `Order()`.
  - H2(m): Implemented using hash_to_field from {{!HASH-TO-CURVE, Section 5.3}}
    using L = 48, `expand_message_xmd` with SHA-256, DST = contextString || "chal", and
    prime modulus equal to `Order()`.
  - H3(m): Implemented using hash_to_field from {{!HASH-TO-CURVE, Section 5.3}}
    using L = 48, `expand_message_xmd` with SHA-256, DST = contextString || "nonce", and
    prime modulus equal to `Order()`.
  - H4(m): Implemented by computing H(contextString \|\| "msg" \|\| m).
  - H5(m): Implemented by computing H(contextString \|\| "com" \|\| m).

Signature verification is as specified in {{prime-order-verify}}.

# Security Considerations {#sec-considerations}

A security analysis of FROST exists in {{FROST20}} and {{Schnorr21}}. The protocol as specified
in this document assumes the following threat model.

* Trusted dealer. The dealer that performs key generation is trusted to follow
the protocol, although signers still are able to verify the consistency of their
shares via a VSS (verifiable secret sharing) step; see {{dep-vss}}.

* Unforgeability assuming at most `(MIN_SIGNERS-1)` corrupted signers. So long as an adversary
corrupts fewer than `MIN_SIGNERS` signers, the scheme remains secure against Existential
Unforgeability Under Chosen Message Attack (EUF-CMA) attacks, as defined in {{BonehShoup}},
Definition 13.2.

* Coordinator. We assume the Coordinator at the time of signing does not perform a
denial of service attack. A denial of service would include any action which either
prevents the protocol from completing or causing the resulting signature to be invalid.
Such actions for the latter include sending inconsistent values to signers,
such as messages or the set of individual commitments. Note that the Coordinator
is *not* trusted with any private information and communication at the time of signing
can be performed over a public but reliable channel.

The protocol as specified in this document does not target the following goals:

* Post quantum security. FROST, like plain Schnorr signatures, requires the hardness of the Discrete Logarithm Problem.
* Robustness. In the case of failure, FROST requires aborting the protocol.
* Downgrade prevention. All signers in the protocol are assumed to agree on what algorithms to use.
* Metadata protection. If protection for metadata is desired, a higher-level communication
channel can be used to facilitate key generation and signing.

The rest of this section documents issues particular to implementations or deployments.

## Nonce Reuse Attacks

{{dep-nonces}} describes the procedure that signers use to produce nonces during
the first round of singing. The randomness produced in this procedure MUST be sampled
uniformly at random. The resulting nonces produced via `nonce_generate` are indistinguishable
from values sampled uniformly at random. This requirement is necessary to avoid
replay attacks initiated by other signers, which allow for a complete key-recovery attack.
The Coordinator MAY further hedge against nonce reuse attacks by tracking signer nonce
commitments used for a given group key, at the cost of additional state.

## Protocol Failures

We do not specify what implementations should do when the protocol fails, other than requiring that
the protocol abort. Examples of viable failure include when a verification check returns invalid or
if the underlying transport failed to deliver the required messages.

## Removing the Coordinator Role {#no-coordinator}

In some settings, it may be desirable to omit the role of the Coordinator entirely.
Doing so does not change the security implications of FROST, but instead simply
requires each signer to communicate with all other signers. We loosely
describe how to perform FROST signing among signers without this coordinator role.
We assume that every signer receives as input from an external source the
message to be signed prior to performing the protocol.

Every signer begins by performing `commit()` as is done in the setting
where a Coordinator is used. However, instead of sending the commitment
to the Coordinator, every signer instead will publish
this commitment to every other signer. Then, in the second round, signers will already have
sufficient information to perform signing. They will directly perform `sign()`.
All signers will then publish their signature shares to one another. After having
received all signature shares from all other signers, each signer will then perform
`verify_signature_share` and then `aggregate` directly.

The requirements for the underlying network channel remain the same in the setting
where all signers play the role of the Coordinator, in that all messages that
are exchanged are public and so the channel simply must be reliable. However, in
the setting that a player attempts to split the view of all other players by
sending disjoint values to a subset of players, the signing operation will output
an invalid signature. To avoid this denial of service, implementations may wish
to define a mechanism where messages are authenticated, so that cheating players
can be identified and excluded.

## Input Message Validation {#message-validation}

Some applications may require that signers only process messages of a certain
structure. For example, in digital currency applications wherein multiple
signers may collectively sign a transaction, it is reasonable to require that
each signer check the input message to be a syntactically valid transaction.
As another example, use of threshold signatures in TLS {{?TLS=RFC8446}} to produce
signatures of transcript hashes might require that signers check that the input
message is a valid TLS transcript from which the corresponding transcript hash
can be derived.

In general, input message validation is an application-specific consideration
that varies based on the use case and threat model. However, it is RECOMMENDED
that applications take additional precautions and validate inputs so that signers
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

# Schnorr Signature Verification for Prime-Order Groups {#prime-order-verify}

This section contains a routine for verifying Schnorr signatures with validated inputs.
Specifically, it assumes that signature R component and public key belong to the
prime-order group.

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
shares of s, denoted `s_i` for `i = 0, ..., MAX_SIGNERS`, to be sent to all `MAX_SIGNERS` signers.
This operation is specified in the `trusted_dealer_keygen` algorithm. The mathematical relation
between the secret key `s` and the `MAX_SIGNER` secret shares is formalized in the `secret_share_combine(shares)`
algorithm, defined in {{dep-shamir}}.

The dealer that performs `trusted_dealer_keygen` is trusted to 1) generate good randomness, and 2) delete secret values after distributing shares to each participant, and 3) keep secret values confidential.

~~~
  Inputs:
  - secret_key, a group secret, a Scalar, that MUST be derived from at least Ns bytes of entropy
  - MAX_SIGNERS, the number of shares to generate, an integer
  - MIN_SIGNERS, the threshold of the secret sharing scheme, an integer

  Outputs:
  - signer_private_keys, MAX_SIGNERS shares of the secret key s, each a tuple
    consisting of the signer identifier and the key share (a Scalar).
  - vss_commitment, a vector commitment of Elements in G, to each of the coefficients
    in the polynomial defined by secret_key_shares and whose first element is
    G.ScalarBaseMult(s).

  def trusted_dealer_keygen(secret_key, MAX_SIGNERS, MIN_SIGNERS):
    signer_private_keys, coefficients = secret_share_shard(secret_key, MAX_SIGNERS, MIN_SIGNERS)
    vss_commitment = vss_commit(coefficients):
    PK = G.ScalarBaseMult(secret_key)
    return signer_private_keys, vss_commitment
~~~

It is assumed the dealer then sends one secret key share to each of the `NUM_SIGNERS` signers, along with `vss_commitment`.
After receiving their secret key share and `vss_commitment`, signers MUST abort if they do not have the same view of `vss_commitment`.
Otherwise, each signer MUST perform `vss_verify(secret_key_share_i, vss_commitment)`, and abort if the check fails.
The trusted dealer MUST delete the secret_key and secret_key_shares upon completion.

Use of this method for key generation requires a mutually authenticated secure channel
between the dealer and signers to send secret key shares, wherein the channel provides confidentiality
and integrity. Mutually authenticated TLS is one possible deployment option.

## Shamir Secret Sharing {#dep-shamir}

In Shamir secret sharing, a dealer distributes a secret `Scalar` `s` to `n` signers
in such a way that any cooperating subset of `MIN_SIGNERS` signers can recover the
secret. There are two basic steps in this scheme: (1) splitting a secret into
multiple shares, and (2) combining shares to reveal the resulting secret.

This secret sharing scheme works over any field `F`. In this specification, `F` is
the scalar field of the prime-order group `G`.

The procedure for splitting a secret into shares is as follows.

~~~
  secret_share_shard(s, MAX_SIGNERS, MIN_SIGNERS):

  Inputs:
  - s, secret value to be shared, a Scalar
  - MAX_SIGNERS, the number of shares to generate, an integer less than 2^16
  - MIN_SIGNERS, the threshold of the secret sharing scheme, an integer greater than 0

  Outputs:
  - secret_key_shares, A list of MAX_SIGNERS number of secret shares, each a tuple
    consisting of the signer identifier and the key share (a Scalar)
  - coefficients, a vector of MIN_SIGNERS coefficients which uniquely determine a polynomial f.

  Errors:
  - "invalid parameters", if MIN_SIGNERS > MAX_SIGNERS or if MIN_SIGNERS is less than 2

  def secret_share_shard(s, MAX_SIGNERS, MIN_SIGNERS):
    if MIN_SIGNERS > MAX_SIGNERS:
      raise "invalid parameters"
    if MIN_SIGNERS < 2:
      raise "invalid parameters"

    # Generate random coefficients for the polynomial, yielding
    # a polynomial of degree at most (MIN_SIGNERS - 1)
    coefficients = [s]
    for i in range(1, MIN_SIGNERS):
      coefficients.append(G.RandomScalar())

    # Evaluate the polynomial for each point x=1,...,n
    secret_key_shares = []
    for x_i in range(1, MAX_SIGNERS + 1):
      y_i = polynomial_evaluate(Scalar(x_i), coefficients)
      secret_key_share_i = (x_i, y_i)
      secret_key_share.append(secret_key_share_i)
    return secret_key_shares, coefficients
~~~

Let `points` be the output of this function. The i-th element in `points` is
the share for the i-th signer, which is the randomly generated polynomial
evaluated at coordinate `i`. We denote a secret share as the tuple `(i, points[i])`,
and the list of these shares as `shares`.
`i` MUST never equal `0`; recall that `f(0) = s`, where `f` is the polynomial defined in a Shamir secret sharing operation.

The procedure for combining a `shares` list of length `MIN_SIGNERS` to recover the
secret `s` is as follows; the algorithm `polynomial_interpolation is defined in {{dep-polynomial-interpolate}}`.

~~~
  secret_share_combine(shares):

  Inputs:
  - shares, a list of at minimum MIN_SIGNERS secret shares, each a tuple (i, f(i))
    where i and f(i) are Scalars

  Outputs: The resulting secret s, a Scalar, that was previously split into shares

  Errors:
  - "invalid parameters", if fewer than MIN_SIGNERS input shares are provided

  def secret_share_combine(shares):
    if len(shares) < MIN_SIGNERS:
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
    L = []
    for point in points:
      L.append(point.x)

    f_zero = Scalar(0)
    for point in points:
      delta = point.y * derive_lagrange_coefficient(point.x, L)
      f_zero = f_zero + delta

    return f_zero
~~~

## Verifiable Secret Sharing {#dep-vss}

Feldman's Verifiable Secret Sharing (VSS) builds upon Shamir secret sharing,
adding a verification step to demonstrate the consistency of a signer's
share with a public commitment to the polynomial `f` for which the secret `s`
is the constant term. This check ensures that all signers have a point
(their share) on the same polynomial, ensuring that they can later reconstruct
the correct secret.

The procedure for committing to a polynomial `f` of degree at most `MIN_SIGNERS-1` is as follows.

~~~
  vss_commit(coeffs):

  Inputs:
  - coeffs, a vector of the MIN_SIGNERS coefficients which uniquely determine
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

The procedure for verification of a signer's share is as follows.
If `vss_verify` fails, the signer MUST abort the protocol, and failure should be investigated out of band.

~~~
  vss_verify(share_i, vss_commitment):

  Inputs:
  - share_i: A tuple of the form (i, sk_i), where i indicates the signer
    identifier, and sk_i the signer's secret key, a secret share of the
    constant term of f, where sk_i is a Scalar.
  - vss_commitment: A VSS commitment to a secret polynomial f, a vector commitment
    to each of the coefficients in coeffs, where each element of the vector commitment
    is an Element

  Outputs: 1 if sk_i is valid, and 0 otherwise

  vss_verify(share_i, commitment)
    (i, sk_i) = share_i
    S_i = ScalarBaseMult(sk_i)
    S_i' = G.Identity()
    for j in range(0, MIN_SIGNERS):
      S_i' += G.ScalarMult(vss_commitment[j], pow(i, j))
    if S_i == S_i':
      return 1
    return 0
~~~

We now define how the Coordinator and signers can derive group info,
which is an input into the FROST signing protocol.

~~~
    derive_group_info(MAX_SIGNERS, MIN_SIGNERS, vss_commitment):

    Inputs:
    - MAX_SIGNERS, the number of shares to generate, an integer
    - MIN_SIGNERS, the threshold of the secret sharing scheme, an integer
    - vss_commitment: A VSS commitment to a secret polynomial f, a vector commitment to each of the
    coefficients in coeffs, where each element of the vector commitment is an Element in G.

    Outputs:
    - PK, the public key representing the group, an Element.
    - signer_public_keys, a list of MAX_SIGNERS public keys PK_i for i=1,...,MAX_SIGNERS,
      where each PK_i is the public key, an Element, for signer i.

    derive_group_info(MAX_SIGNERS, MIN_SIGNERS, vss_commitment)
      PK = vss_commitment[0]
      signer_public_keys = []
      for i in range(1, MAX_SIGNERS+1):
        PK_i = G.Identity()
        for j in range(0, MIN_SIGNERS):
          PK_i += G.ScalarMult(vss_commitment[j], pow(i, j))
        signer_public_keys.append(PK_i)
      return PK, signer_public_keys
~~~

# Random Scalar Generation {#random-scalar}

Two popular algorithms for generating a random integer uniformly distributed in
the range \[0, G.Order() -1\] are as follows:

## Rejection Sampling

Generate a random byte array with `Ns` bytes, and attempt to map to a Scalar
by calling `DeserializeScalar` in constant time. If it succeeds, return the
result. If it fails, try again with another random byte array, until the
procedure succeeds. Failure to implement this in constant time can leak information
about the underlying corresponding Scalar.

Note the that the Scalar size might be some bits smaller than the array size,
which can result in the loop iterating more times than required. In that case
it's acceptable to set the high-order bits to 0 before calling `DeserializeScalar`,
but care must be taken to not set to zero more bits than required. For example,
in the `FROST(Ed25519, SHA-512)` ciphersuite, the order has 253 bits while
the array has 256; thus the top 3 bits of the last byte can be set to zero.

## Wide Reduction

Generate a random byte array with `L = ceil(((3 * ceil(log2(G.Order()))) / 2) / 8)`
bytes, and interpret it as an integer; reduce the integer modulo `G.Order()` and return the
result. See {{Section 5 of HASH-TO-CURVE}} for the underlying derivation of `L`.


# Test Vectors

This section contains test vectors for all ciphersuites listed in {{ciphersuites}}.
All `Element` and `Scalar` values are represented in serialized form and encoded in
hexadecimal strings. Signatures are represented as the concatenation of their
constituent parts. The input message to be signed is also encoded as a hexadecimal
string.

Each test vector consists of the following information.

- Configuration. This lists the fixed parameters for the particular instantiation
  of FROST, including MAX_SIGNERS, MIN_SIGNERS, and NUM_SIGNERS.
- Group input parameters. This lists the group secret key and shared public key,
  generated by a trusted dealer as described in {{dep-dealer}}, as well as the
  input message to be signed. All values are encoded as hexadecimal strings.
- Signer input parameters. This lists the signing key share for each of the
  NUM_SIGNERS signers.
- Round one parameters and outputs. This lists the NUM_SIGNERS participants engaged
  in the protocol, identified by their integer identifier, and for each participant:
  the hiding and binding commitment values produced in {{frost-round-one}}; the randomness
  values used to derive the commitment nonces in `nonce_generate`; the resulting group
  binding factor input computed in part from the group commitment list encoded as
  described in {{dep-encoding}}; and group binding factor as computed in {{frost-round-two}}).
- Round two parameters and outputs. This lists the NUM_SIGNERS participants engaged
  in the protocol, identified by their integer identifier, along with their corresponding
  output signature share as produced in {{frost-round-two}}.
- Final output. This lists the aggregate signature as produced in {{frost-aggregation}}.

## FROST(Ed25519, SHA-512)

~~~
// Configuration information
MAX_SIGNERS: 3
MIN_SIGNERS: 2
NUM_SIGNERS: 2

// Group input parameters
group_secret_key: 7b1c33d3f5291d85de664833beb1ad469f7fb6025a0ec78b3a7
90c6e13a98304
group_public_key: 15d21ccd7ee42959562fc8aa63224c8851fb3ec85a3faf66040
d380fb9738673
message: 74657374

// Signer input parameters
S1 signer_share: 929dcc590407aae7d388761cddb0c0db6f5627aea8e217f4a033
f2ec83d93509
S2 signer_share: a91e66e012e4364ac9aaa405fcafd370402d9859f7b6685c07ee
d76bf409e80d
S3 signer_share: d3cb090a075eb154e82fdb4b3cb507f110040905468bb9c46da8
bdea643a9a02

// Round one parameters
participants: 1,3

// Signer round one outputs
S1 hiding_nonce_randomness: d69890885638925b251724b48c40b8a500f838fe8
b1b0851a2da094969c1ea3a
S1 binding_nonce_randomness: 7dd4f7213c8c1f02889cce1300212851f4fd33c9
e860ffb757018ad620702744
S1 hiding_nonce: 22da11c1bff06d2bdffc76f39287e5eff97e517033c938a0ca9a
dcbbda830a04
S1 binding_nonce: bd34fb04c78b38b6a4cca2477d25310a5d98a41383c5ac5dafb
a7c4cf86ac001
S1 hiding_nonce_commitment: 0c1c0c64794d7964453bf711a08db8a912de6fefb
b12956b087a5049da631a4b
S1 binding_nonce_commitment: 3fe43acbaed63891f6c3d07684a77228bc7c7909
2fab912290b2f37f8a7a6423
S1 binding_factor_input: 25120720c3a416e292edfb0510780bc84eb734347a5f
d84dd46d0dcbf3a21d21a23a776628859678a968acc8c8564c4641a1fd4b29a12d536
7ca12ab10b6b497ae5c25ded33580a5d6006bec9c4ae92099f9b1f1839fd697ee2301
4e77c3e82bb034dc39d267c77d61792c8df7c747a7f57e8260dd9066c68edec3b4648
a65570001
S1 binding_factor: 8d626a94915455d59acf42fdb6f9d65b05037885e542de4175
c9f4b7f9429b0d
S3 hiding_nonce_randomness: 5d9f143b518509a5bd45c2c71b8dee7d9bb452710
d52bb6713dbf0068eade977
S3 binding_nonce_randomness: 091e5807702361c0359ae27d37b669dd2fa65ec8
67d2cc7f72ae14454b3423a9
S3 hiding_nonce: bcffd47c9e926493c227dadb3f0eca959346860ae6fb4a438030
22aea31e6306
S3 binding_nonce: 6f605d6efcb3452d222ac8a451fea6fc49c4bc785d9a0897114
53361481ab007
S3 hiding_nonce_commitment: 29b562d1ee75f969c13980b03277874d9f0de3932
46560cd001e04ec6b08f773
S3 binding_nonce_commitment: 1b32c2e7796c38b5fe25c50377cdd161608fe793
6a5a8af0b0c1af7883350229
S3 binding_factor_input: 25120720c3a416e292edfb0510780bc84eb734347a5f
d84dd46d0dcbf3a21d21a23a776628859678a968acc8c8564c4641a1fd4b29a12d536
7ca12ab10b6b497ae5c25ded33580a5d6006bec9c4ae92099f9b1f1839fd697ee2301
4e77c3e82bb034dc39d267c77d61792c8df7c747a7f57e8260dd9066c68edec3b4648
a65570003
S3 binding_factor: 8fc7702fb3f31b2cbf2184344e87c77450a6a66e3eaa4abe05
a1d983f679320a

// Round two parameters
participants: 1,3

// Signer round two outputs
S1 sig_share: 8d6c5ad9fafdc2b7f54c1c8e3f8b732ff624069f6b01093109790ca
e917df30d
S3 sig_share: c3978db4ec26aba506664da6fa005da3582f6781823a0c217c5d203
22de62404

sig: ab4fcc20920987ac7c8f3694b49fcbfe0ce1fb273d5381de89d8a92f2295d74e
6330f230cdc15b05261672915b92f1bd4e546d20ee3b155285d62ce0be631802
~~~

## FROST(Ed448, SHAKE256)

~~~
// Configuration information
MAX_SIGNERS: 3
MIN_SIGNERS: 2
NUM_SIGNERS: 2

// Group input parameters
group_secret_key: 6298e1eef3c379392caaed061ed8a31033c9e9e3420726f23b4
04158a401cd9df24632adfe6b418dc942d8a091817dd8bd70e1c72ba52f3c00
group_public_key: 3832f82fda00ff5365b0376df705675b63d2a93c24c6e81d408
01ba265632be10f443f95968fadb70d10786827f30dc001c8d0f9b7c1d1b000
message: 74657374

// Signer input parameters
S1 signer_share: 4a2b2f5858a932ad3d3b18bd16e76ced3070d72fd79ae4402df2
01f525e754716a1bc1b87a502297f2a99d89ea054e0018eb55d39562fd0100
S2 signer_share: 2503d56c4f516444a45b080182b8a2ebbe4d9b2ab509f25308c8
8c0ea7ccdc44e2ef4fc4f63403a11b116372438a1e287265cadeff1fcb0700
S3 signer_share: 00db7a8146f995db0a7cf844ed89d8e94c2b5f259378ff66e39d
172828b264185ac4decf7219e4aa4478285b9c0eef4fccdf3eea69dd980d00

// Round one parameters
participants: 1,3

// Signer round one outputs
S1 hiding_nonce_randomness: bbb58399b52897419bd2b044e17145f068f878228
e0ce0c95e522a2102eeea62
S1 binding_nonce_randomness: 58a16ba8afe654b72278ac3cbd2d8c135a887153
9884c6e75aa569e5ec6367d2
S1 hiding_nonce: 8c8144102050318838f2bac501eced275b9299e6975afb3e88d0
aa1add0a964cf94d22d525033e55c24948ae0fc3440c270640bb4349552300
S1 binding_nonce: b6978464ff1d5def44907f0c7749806725e4ea7ba93057329a8
8efe5ca003f817fa02705bc42eb6658672af41d17870e40b70ce1834d383600
S1 hiding_nonce_commitment: 9d94192aa8b9ef05ae4da111ab22edd3ad81cba37
c45b2788807e65d2e139ce6f4808bd11b75282c12cfbf92e2bc71d00a1302f350ff15
9b00
S1 binding_nonce_commitment: aff44f339b558999eac4cbd487f4848443897843
6e828b0e5d9fdd7fc07e6f4c1e2c4ba5d3ae1adb76c4966ead7f24b617bc8a0c9c8d1
7c800
S1 binding_factor_input: 766a004ac6e87a2fa70f2095b19596ac33b94e2f6803
e1a5b8fa8ea5adaf3e7989b2c167a38a42a1693ad69cfd674e089a498672753563d53
54654ba106d5fdffb134a8917fae91d412164436f734b95572af6208605744400c6ff
9a60fa2ce8fb7f3213414c32e347ee2e29e3d17654ef023eed61051586783022cc4cf
a471ee6fa0872880d19b29dc14fac071f7fe467f4646059038286172bd78821d8a649
43790554f7851f4ef3311fdadf8b54cb5788cb7f4504305da6be864ae899f5e7d1c5f
ae9174cb53fb2640d2c0e3e213c4094e411d6155fcf88773d8a1270ae8aa03563c900
01
S1 binding_factor: abaf4a2a2eadff424a66133827afdfa3296c220382d7dc0870
a6dfbe953fe72a92df45207227e1231113bea7f32b7c80b031f8a615bbec3800
S3 hiding_nonce_randomness: e3f570151303da4e5a1202e5b417b5d30f98c0f82
ef94e7bfea5b820f22d0995
S3 binding_nonce_randomness: d1a579ce9c0b06237ac80ec0e0e8284c0492e5fb
09dfec1c34f4178f74adf916
S3 hiding_nonce: 3e07736968bdeaf3e6db8b334475c6fafe2928243a437e4ede9f
b4c9d9be58227d5a684a1160c6ce9260611dfb2103b11add29a91df0900800
S3 binding_nonce: 7805cd0423a659f4d20fbdd6f8a88b828de527f75b31ddd588d
2ba683431dcd944ec81892f9cbe039852af8b00d9d2e9a3ba6b0cf9748e1300
S3 hiding_nonce_commitment: b3c28f9c6d1ec92069d8c27f4661c8b33f3036183
9a3ba12f8d6f3a953f5853fbf10fd53cc91cf6a2c3cff16c9fb8481d469159212ead5
a480
S3 binding_nonce_commitment: 26ab246280655b42a5dedd6aba9680889721ab02
afd9072f6ae8a18239cc8045331cf3874c171dab87d52fae31b8dc48d063c63c9f77d
1e380
S3 binding_factor_input: 766a004ac6e87a2fa70f2095b19596ac33b94e2f6803
e1a5b8fa8ea5adaf3e7989b2c167a38a42a1693ad69cfd674e089a498672753563d53
54654ba106d5fdffb134a8917fae91d412164436f734b95572af6208605744400c6ff
9a60fa2ce8fb7f3213414c32e347ee2e29e3d17654ef023eed61051586783022cc4cf
a471ee6fa0872880d19b29dc14fac071f7fe467f4646059038286172bd78821d8a649
43790554f7851f4ef3311fdadf8b54cb5788cb7f4504305da6be864ae899f5e7d1c5f
ae9174cb53fb2640d2c0e3e213c4094e411d6155fcf88773d8a1270ae8aa03563c900
03
S3 binding_factor: e426c609db3e5c5174b7165b5b6584dbf38fe9ccdd84e91aab
ef28047f667661894368c2351cba15db2c3245d8d061a731b1ccea796e7e0900

// Round two parameters
participants: 1,3

// Signer round two outputs
S1 sig_share: 26875caf430aa6ea61e97f477412579deff9dc895cd385812df5968
9c5a3ccf0a728b4d72f8db62d69556ded456522eed3d93c586390d22a00
S3 sig_share: e7053a6571e53e0729d4e53a76ba3c1d069b8e4e5079d28333a86ce
496c6f5cd0afd55b0068dd947e232abb8f9418776dc94e5857fcb1e0600

sig: 38e91000329fca9f1b2f74fc642947bbc7b787cbbd9183f98e70e3eef3bd384b
f1c4cb50e063fd4e73aaf3321549126a39a4f86405831afa000d8d9614b5efe4f18ab
d6582eacc93baf5946bd8ac4c5805619d036e5c6ac2beb2250a88361a90754b8818a6
3fa7a964b06e22dee25bf13000
~~~

## FROST(ristretto255, SHA-512)

~~~
// Configuration information
MAX_SIGNERS: 3
MIN_SIGNERS: 2
NUM_SIGNERS: 2

// Group input parameters
group_secret_key: 1b25a55e463cfd15cf14a5d3acc3d15053f08da49c8afcf3ab2
65f2ebc4f970b
group_public_key: e2a62f39eede11269e3bd5a7d97554f5ca384f9f6d3dd9c3c0d
05083c7254f57
message: 74657374

// Signer input parameters
S1 signer_share: 5c3430d391552f6e60ecdc093ff9f6f4488756aa6cebdbad75a7
68010b8f830e
S2 signer_share: b06fc5eac20b4f6e1b271d9df2343d843e1e1fb03c4cbb673f28
72d459ce6f01
S3 signer_share: f17e505f0e2581c6acfe54d3846a622834b5e7b50cad9a2109a9
7ba7a80d5c04

// Round one parameters
participants: 1,3

// Signer round one outputs
S1 hiding_nonce_randomness: 0926ddfc444fe15f994867178bad8535b7d4e1316
5004cf205eb3f2176643fb3
S1 binding_nonce_randomness: 22b0cb53ade9f7f75a8da147de631855bae11992
91e9d571d6aa4b2bf2069569
S1 hiding_nonce: 85e80dae5ec5be434f294c4398931ad9b309913f5c314f2f527b
18c155c1740b
S1 binding_nonce: 9f95313c636709d60d1a12f3588b9492cf84e31aafe0ac73a6d
e3776fd4d0906
S1 hiding_nonce_commitment: e8c5b08e5bd2070d892d710aee98a1a2fccb06818
4415374469a682621a59601
S1 binding_nonce_commitment: b68b6e082c64f0c6f5c7d8fe065326a52c20125e
8911ebb865ad6301be430655
S1 binding_factor_input: fe9082dcc1ae1ae11380ac4cf0b6e2770af565ff5af9
016254dc7c9d4869cbae0f6e4d94b23e5781b91bc74a25e0c773446b2640290d07c83
f0b067ff870a801c9fca21a57fee3b3f0e9bf6d097c71217f827465d33024527220b3
70d5fa8c3487a66d246ffbcd1079b9f2b832c3386b5eb44ca3110daeadd872af0629e
9a8860001
S1 binding_factor: 436c215db8ac1d4cfae65b5cd894e4d9734e5ebbfcf8658e76
37058d8d31050f
S3 hiding_nonce_randomness: 0a39da8b5c790efed08f60b244a028f8097a87211
16a9a26f079726e1828a798
S3 binding_nonce_randomness: 107de7423a0e42be6c9d37a1600d41996aa542d4
73f2062e0aa9a3e98d0110bc
S3 hiding_nonce: 24e46ffd4b22e7f9105555049f2a5122cc45ba430750a5525173
9b14365f0e01
S3 binding_nonce: e510a0b178668d39d65ae03f4a4382ac4bd5279fdc88559d2ee
b906827344606
S3 hiding_nonce_commitment: 1cfb88d54435248946f93a9e41ab58e6a9b94e290
c0189e4c54aa24df0eaa257
S3 binding_nonce_commitment: 661099702939493db834aea5663a8edc986b7765
55e3acbeb3fb1813145fc850
S3 binding_factor_input: fe9082dcc1ae1ae11380ac4cf0b6e2770af565ff5af9
016254dc7c9d4869cbae0f6e4d94b23e5781b91bc74a25e0c773446b2640290d07c83
f0b067ff870a801c9fca21a57fee3b3f0e9bf6d097c71217f827465d33024527220b3
70d5fa8c3487a66d246ffbcd1079b9f2b832c3386b5eb44ca3110daeadd872af0629e
9a8860003
S3 binding_factor: b05695453984f989313ef6e2026fea7220ef46b6417133a6fb
a81992fb515506

// Round two parameters
participants: 1,3

// Signer round two outputs
S1 sig_share: 4a54069490efb9d941cead32a5ece0862a6ba1294de29b4d8e8f4df
18990ae01
S3 sig_share: 1a5a7a501ee0b792060d96b1c0fe2c40e92fbb2beb5e3665fe4c52d
4b1e8a003

sig: 96b4d57119b8451a9c08f1d23203654509987bf8fa577d03a283f0d239ac9540
64ae80e4aecf716c48db43e465eb0dc7139b5c553841d2b28cdc9fc53b794f05
~~~

## FROST(P-256, SHA-256)

~~~
// Configuration information
MAX_SIGNERS: 3
MIN_SIGNERS: 2
NUM_SIGNERS: 2

// Group input parameters
group_secret_key: 8ba9bba2e0fd8c4767154d35a0b7562244a4aaf6f36c8fb8735
fa48b301bd8de
group_public_key: 023a309ad94e9fe8a7ba45dfc58f38bf091959d3c99cfbd02b4
dc00585ec45ab70
message: 74657374

// Signer input parameters
S1 signer_share: 0c9c1a0fe806c184add50bbdcac913dda73e482daf95dcb9f35d
bb0d8a9f7731
S2 signer_share: 8d8e787bef0ff6c2f494ca45f4dad198c6bee01212d6c8406715
9c52e1863ad5
S3 signer_share: 0e80d6e8f6192c003b5488ce1eec8f5429587d48cf001541e713
b2d53c09d928

// Round one parameters
participants: 1,3

// Signer round one outputs
S1 hiding_nonce_randomness: 8dd17d1ba3dfc7de3b5c5451c291435742c9da8fc
a5d347a80fdfa699d3bbf02
S1 binding_nonce_randomness: f235d4e52cbcce7f7ad081bd2cb9afdfb94fc17a
d2fd82b570e68db74cf84d9f
S1 hiding_nonce: fb5fa336237c7e365738bc2aaea5ddca53b86e4ae18a6c92fea5
261c1a0cac44
S1 binding_nonce: eadc82592a64742e9516202e6cec4fd61dd37148730036fea2a
28b6c71974c92
S1 hiding_nonce_commitment: 0356b53a2383c9d4762b4dfe83e76d53bb3e45681
bcfd445499b2948863ff696cc
S1 binding_nonce_commitment: 021d53a49180d7544da34dfdfe6118716521358c
6d57c39fafb33fb07b96a3f0cd
S1 binding_factor_input: 3617acb73b44df565fbcbbbd1824142c473ad1d6c800
7c4b72a298d1eaae57663f5d996c134493ffebe414006e5b8eb0c3dce1ed80f0a2b70
dcbbcc4f58cc44c0001
S1 binding_factor: 8406e9b5d5fc1ef44e65e83c7795a32e84d6d9fac3fca8bc0b
cbd8901e4e985a
S3 hiding_nonce_randomness: 53ff4ae3c3305e420c3219af0225196ebcfc1285d
1d5882c40f1b99bc363553a
S3 binding_nonce_randomness: 21e912ac76cd5d9454119d226468f853509f7885
1cd8867c912f990e4b9ddb9c
S3 hiding_nonce: 39e7f50f4775d62410bd92a4ff80424ef964b3fbf5d4fb5cab96
13110dae91cb
S3 binding_nonce: 4e99ab19a3972340d628a4595b2ad56617fad340ae29cb40a48
99979fbdece77
S3 hiding_nonce_commitment: 020ca7c3cdc49e359d9ab49c5eb6c9776a4c41003
b5ef202e993629b734b3ad0e8
S3 binding_nonce_commitment: 037c92d4f8ceaf9b0fdcf61e34f8d1d5477cb1aa
7da6fdff86e452106345ffb2c1
S3 binding_factor_input: 3617acb73b44df565fbcbbbd1824142c473ad1d6c800
7c4b72a298d1eaae57663f5d996c134493ffebe414006e5b8eb0c3dce1ed80f0a2b70
dcbbcc4f58cc44c0003
S3 binding_factor: 0df2d4b4b6221362066082121f6906e8e07b44cb056fbd157f
e8ad99f241dc3b

// Round two parameters
participants: 1,3

// Signer round two outputs
S1 sig_share: 88e01f9731f24e4fc97e105517df81c0fff2d2f412f9818960d88aa
bb5fd3e06
S3 sig_share: 7940e2387e0c5918ba162e5d69742ce291622b1fbcb1db244a3631f
406b76a24

sig: 034513f8b81b9d933364cafacaa0fa49b1769e10af2abbea399c7a050550bd72
12022101d0affea76783943eb28153aea3d46e03662893be28b754f1dcc05182d9
~~~

## FROST(secp256k1, SHA-256)

~~~
// Configuration information
MAX_SIGNERS: 3
MIN_SIGNERS: 2
NUM_SIGNERS: 2

// Group input parameters
group_secret_key: 0d004150d27c3bf2a42f312683d35fac7394b1e9e318249c1bf
e7f0795a83114
group_public_key: 02f37c34b66ced1fb51c34a90bdae006901f10625cc06c4f646
63b0eae87d87b4f
message: 74657374

// Signer input parameters
S1 signer_share: 08f89ffe80ac94dcb920c26f3f46140bfc7f95b493f8310f5fc1
ea2b01f4254c
S2 signer_share: 04f0feac2edcedc6ce1253b7fab8c86b856a797f44d83d82a385
554e6e401984
S3 signer_share: 00e95d59dd0d46b0e303e500b62b7ccb0e555d49f5b849f5e748
c071da8c0dbc

// Round one parameters
participants: 1,3

// Signer round one outputs
S1 hiding_nonce_randomness: 6c2ffe6acdeab388f99dacf4b1d0f54c4347b6704
7475c7240f8321a6b445632
S1 binding_nonce_randomness: 1f9cd4f714c7f313b817ed513111b09d009eca42
9ec31556089ce21282654cbe
S1 hiding_nonce: 13ccf4cb42a93108118ae3532c2c678d23f01c76b3c314f560e4
767b9622c8a5
S1 binding_nonce: 0cd29b90993d04017874f75a3f283f9f079272f2fea869aad20
406a697ba0494
S1 hiding_nonce_commitment: 0217faaea690aac421a485c87e60b721334790626
5bf7cf39cfc3fa8ef59b9996e
S1 binding_nonce_commitment: 02120026132ac451efb51f6773553aecf02d3479
0d82b8dcc2e05a71b387f3676f
S1 binding_factor_input: d759fa818c284537bbb2efa2d7247eac9232b7b992cd
49237106acab251dd95484130ad7927513c6fea81f43852f1637c9c7a4b559c74033c
b215802ca0d4bfd0001
S1 binding_factor: b092be662b30bac484793b2e5c260382f93568442132d00d83
5042ba1670fccc
S3 hiding_nonce_randomness: 2188362baee05233f7edfe953a68a03ed962cdf39
becf6f243dffff27a2dd67d
S3 binding_nonce_randomness: 745905d509462c1f6fc64c7c88f508102afaa58a
ee4c49f2dfb151445284c3c7
S3 hiding_nonce: c3446606d68e818871c14e94863d625af11c04bb40437c64d286
9ccf245d88cf
S3 binding_nonce: ce020ade05afe77ecd65cbae78af54f72a4691cb09fa1c159bd
5d549800595ab
S3 hiding_nonce_commitment: 0388bc09eea4059abcfd7dc093ddcc49183e2006f
a10da1ed63ee095205aa39b21
S3 binding_nonce_commitment: 02910d9826b8cbf2571a9ff9a9f1476eb945eefc
66729dc3a7e163133bb4a14db7
S3 binding_factor_input: d759fa818c284537bbb2efa2d7247eac9232b7b992cd
49237106acab251dd95484130ad7927513c6fea81f43852f1637c9c7a4b559c74033c
b215802ca0d4bfd0003
S3 binding_factor: f05ba42ccd8bf4ad5a3b74c05b2cb2ae8e4de904ca1e7c3167
788def077eae24

// Round two parameters
participants: 1,3

// Signer round two outputs
S1 sig_share: c816611ef8cce4422697ac068bf228215379529b883a196735724fc
2f0a9c64b
S3 sig_share: d562cf29bcc9d958104bee38164d39ec4e43cd20cdd1dd36e9d7a45
72df31a89

sig: 03e3c155366f19446a80720d6ed116dae31cd57d70e4d69850152fd61022cd4b
d79d793048b596bd9a36e39a3ea23f620ee70e42d5a6c356625f77958d4e669f93
~~~
