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
S1 hiding_nonce_randomness: ce8b36fa7f2bb0b2b1c827088e9623355535e77d7
164e68c596a6579a17147ad
S1 binding_nonce_randomness: 5065abb4fbaab96cfd92b10b275baa6bf373dbaf
0bf634aae1e2a7384f4872d8
S1 hiding_nonce: d5ac1d6b98e77d65d7e0b68c298d26d993e20fb49ae00617081d
1a5ad76f9807
S1 binding_nonce: 4a0bfc17fc8b0abf93ef509ff961cb28c3ca8b9962f05822555
d1481fb766309
S1 hiding_nonce_commitment: bf43b150806c1d06cb701a533a2d5e51fdd58186a
e1e6b7ac8f22c2a900fdcf7
S1 binding_nonce_commitment: da116609409774040eda206a3134728f2ace4b28
99c71e8a36b93fd36c18f8c5
S1 binding_factor_input: 25120720c3a416e292edfb0510780bc84eb734347a5f
d84dd46d0dcbf3a21d21a23a776628859678a968acc8c8564c4641a1fd4b29a12d536
7ca12ab10b6b4976c9b85cefa255ee05385939c5a720e29efa1ebffce0b9b4bd25e31
0623fa6c40664360670b83e457027f0cedc323f8a86257beae9408f7b68e8a8520552
b014d0001
S1 binding_factor: c85878a4ac252245e92e4230df0a5d1e4c34012d8023c0202c
c8139461959601
S3 hiding_nonce_randomness: 1b892e7c30b93897bad8708f5e9ae83f53a16206d
4fcbc9b8851ebb4d126001b
S3 binding_nonce_randomness: 84b6dae8c850588f2e6f51c7175caef231c00804
35345785ff21aea4d962310c
S3 hiding_nonce: 4c925e6c38ed50fe20b90a9fd649ed476823142d5f4f6ac39178
fba3e308cc06
S3 binding_nonce: 593c9d8673bfd1e8e57ca19aea09556c64a1a8d0d0d90d40ca1
443d02ea82203
S3 hiding_nonce_commitment: 613eccd0a1e7472004c927577718b6d4c6ab0559b
11032e8bc956ec2c3a34db0
S3 binding_nonce_commitment: b24e019652ab57c43fced219bae60421236d5f81
219d8f42576f2257d960304c
S3 binding_factor_input: 25120720c3a416e292edfb0510780bc84eb734347a5f
d84dd46d0dcbf3a21d21a23a776628859678a968acc8c8564c4641a1fd4b29a12d536
7ca12ab10b6b4976c9b85cefa255ee05385939c5a720e29efa1ebffce0b9b4bd25e31
0623fa6c40664360670b83e457027f0cedc323f8a86257beae9408f7b68e8a8520552
b014d0003
S3 binding_factor: a251052142f2d83fc55c471abc2a2f3baaf75392cb07e33d4b
ac24811e520d0f

// Round two parameters
participants: 1,3

// Signer round two outputs
S1 sig_share: e6e305a4373d2da3963317c13360f5b7ee9ec96d69d601a7bb01f16
e4b05a504
S3 sig_share: e8a7a777ee5611b17106f10fc4809a1c2d7f20345e8602388c36c21
e50eabf05

sig: f72232a31f567a4cc6b97f1940f1320186011500ce953b9bb889e5d6a01b2ebf
ce8bad1b26943e54083a08d1f7e08fd41b1eeaa1c75c04df4738b38d9bef640a
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
S1 hiding_nonce: f770bcb22f3c0acac7f09d3b757f13f31b53489776ede2cff944
b4c0cd28bb7dfbd33809e87201e152beeb552292eb748efa5267fa2dcd2000
S1 binding_nonce: d3196c7f14b1a99f1715053c00fa3a30b0fe9cbeb461068c262
b171478458a15598cc1c33cd415a766577996a6efcc520c411abf0280c81600
S1 hiding_nonce_commitment: dc4f663206390fff683379993f127aab5283d689e
b7940f3211f44112919fa67ac2976cf57c05e9f384a38f749eeeaf903a15ec4fa77a9
f900
S1 binding_nonce_commitment: 7e7bdf9d3489da9aa236b80d1ec8b3df9f0f3806
bce5921ce70750628e8db542558d574f998370dd5d347a020aef3e59d4186c0ac9e09
70500
S1 binding_factor_input: 766a004ac6e87a2fa70f2095b19596ac33b94e2f6803
e1a5b8fa8ea5adaf3e7989b2c167a38a42a1693ad69cfd674e089a498672753563d53
54654ba106d5fdffb134a8917fae91d412164436f734b95572af6208605744400c6ff
9a60fa2ce8fb7f3213414c32e347ee2e29e3d17654ef02c9f7802bacad53b0cbe1c4c
f746e7c97c54a848d20c161ce45e5e3f1fd70ff87b897f557b00e52399ed60f12b24b
99357c9c9d22838608b6f87200d4363437df7ab30374d1340b8efe5df213584a933ea
04566da6e3e85c1a0106b213a810cf4150e6a15e2418b352bf13e119c89e3f5ab8600
01
S1 binding_factor: 22d0ed444b4d42554270198e8e4d98fdf1bb3a159efb2254d6
8977f445f54e3fb580eaf40164f357f3ca5b9644de967b73a3497ad7d4e21000
S3 hiding_nonce: 9172a7cea56b7f564ed93116adf078ee013e4160e2687489ea58
0bc6f034f10e58db0b0cdf98bf1d3c85b2eb1f30b8b6df57b3611d205d2e00
S3 binding_nonce: 3b60b4dc036b21441620a36c84b0ec780267a9275b411a495b1
82dc6bfc812d1a21d93142d375b7ed80314d1693b61c1f42e20c575a4530e00
S3 hiding_nonce_commitment: 5150f6389c06c8cc32ab31e6ca15514f2073c91b1
2815b4e91dcc389d234a450bfeaa30e8befe23632f383566d7eb9d904a7530a3be6a9
f300
S3 binding_nonce_commitment: ce7231d5f89f6792f05a16f074e0fad1b6e3b1f2
f5f5e7bad894157cede68b4bc0621910900c59a3c6e1907301ff90a43b8a086aabdd0
ae080
S3 binding_factor_input: 766a004ac6e87a2fa70f2095b19596ac33b94e2f6803
e1a5b8fa8ea5adaf3e7989b2c167a38a42a1693ad69cfd674e089a498672753563d53
54654ba106d5fdffb134a8917fae91d412164436f734b95572af6208605744400c6ff
9a60fa2ce8fb7f3213414c32e347ee2e29e3d17654ef02c9f7802bacad53b0cbe1c4c
f746e7c97c54a848d20c161ce45e5e3f1fd70ff87b897f557b00e52399ed60f12b24b
99357c9c9d22838608b6f87200d4363437df7ab30374d1340b8efe5df213584a933ea
04566da6e3e85c1a0106b213a810cf4150e6a15e2418b352bf13e119c89e3f5ab8600
03
S3 binding_factor: 3e9156d4199b1057494ed34859d9770d9555879c399afed512
459cf8632e312598ad24e3d0e2d7c75a4d7f75e513fa5b7fd1f473d315191900

// Round two parameters
participants: 1,3

// Signer round two outputs
S1 sig_share: 95aeb18a46bac9e239d8eb51a7168da25a000d8a6938e26446c36e5
db88eff9523e0b09934558ddc8b2679bf2f10ed66415df1eb6e38a50700
S3 sig_share: 521672ae547cd95b94a9be55b72a0dfb6938715230304d39017f5a5
4f1333a96da50a0759eea78bdb6b670c8243dbe706cd388763fe4c50b00

sig: f1c2605fc0b724696dff10d2df0ac28939f40dc3d9ba864605462355c139229d
e643a6580e5807994cfcab0796644571c501cab00e85056a00e7c423399b36a33ece8
1aaa75e419a9dc4387edc99682f9e4742c9b1a9c2392cfe30510fd33f069a42dde987
544dabd7ad307a62ae1c6b1300
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
S1 hiding_nonce_randomness: 9453778963b02c19312871ad39c469ee8830fcffe
4c74930b53ea6ae518a3120
S1 binding_nonce_randomness: 6327baa569a5f50c531aa4f00939e98d5bde038f
e09c89b9c3aa6c2853653259
S1 hiding_nonce: 08bf75b4fd26404a83de1ec38f52342ba0cd6b55c0576f78b1f8
4c9e731aeb01
S1 binding_nonce: cf65d10f4f829c2efbf149ddb12fb4784f37595416232ec1c31
d22315955b006
S1 hiding_nonce_commitment: 28892684211b2da6ead36cb5bda3e2c0769e55941
47d0f904880993578dbff71
S1 binding_nonce_commitment: 2a27574b6b5e950103b0965e750f682414754b22
7899438efe4dbb4c61e1a511
S1 binding_factor_input: fe9082dcc1ae1ae11380ac4cf0b6e2770af565ff5af9
016254dc7c9d4869cbae0f6e4d94b23e5781b91bc74a25e0c773446b2640290d07c83
f0b067ff870a8010432e991d0acb1a9024d55902101554e0d9fbd6941c475110c6058
61c43e35b8e2dedba45c7caf32c3ebca15233fdfc2cd2d066412b5bf4c36125f60b80
214b00001
S1 binding_factor: 89c9cc3f3b68d78b63a0c8ade6ec2cb5bbd7735186a9ed9ca1
49f37a0f6d6f09
S3 hiding_nonce_randomness: 8cb06b7b8a6a71473cb67206df4f13f23d6f04180
881052935791409b7de419b
S3 binding_nonce_randomness: 54ec51393863bf26e152b008731e03adcab715dd
eed778776d72a336d2b2931c
S3 hiding_nonce: 40ad573cba0c143b8b1f67bc2cafde55900ed03d1982f6f62307
b8c9e9e69a05
S3 binding_nonce: d0fb7a65d5afb9dd5b581e634ce40c312fd441b3ec3f7d07af5
6352f869ba30c
S3 hiding_nonce_commitment: 4c74b72d409d64ace991810f69520bbb0eab952de
274b800469290c378870908
S3 binding_nonce_commitment: deea03415ef3bba17d59659dcd5b93bcb3f0bcaa
5a693f890b7a929b12726f7b
S3 binding_factor_input: fe9082dcc1ae1ae11380ac4cf0b6e2770af565ff5af9
016254dc7c9d4869cbae0f6e4d94b23e5781b91bc74a25e0c773446b2640290d07c83
f0b067ff870a8010432e991d0acb1a9024d55902101554e0d9fbd6941c475110c6058
61c43e35b8e2dedba45c7caf32c3ebca15233fdfc2cd2d066412b5bf4c36125f60b80
214b00003
S3 binding_factor: 386069362cf74d23c813bcd17233534416023a95ab0b68ecf7
f16d6285a4750c

// Round two parameters
participants: 1,3

// Signer round two outputs
S1 sig_share: 686b92c6d9f7eff00324ac15b312a6338644447250b7f2994c47541
024b72806
S3 sig_share: 5b32372d6d21bc18c6b7e9dbcb11f9eae8c656f945ef1d330e195b9
27276ce0e

sig: 8a495a20d7eed44259cc1072f3698aea787a9a9a72176d6bba18051ab5d45f22
d6c9d3962cb699b1f33e9e4ea02ac0096f0b9b6b96a610cd5a60afa2962df704
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
S1 hiding_nonce_randomness: 202d9d04a1e167d8a275e003711e548932f3ae8d3
c4907c6b522ef0d0f1b8fc1
S1 binding_nonce_randomness: 3089be882f8598ef1c371c996e6eddde68fa4463
c062cf9144e07d2d220de3be
S1 hiding_nonce: c6f58f9d045907c3d5aa3438910627d845a68afa1fe4ea6f1b6c
1f7596bf788c
S1 binding_nonce: e5eaf0eefbcebc13e2507378e1b6bcab280e29c8ad815585e2b
16e7eeebcd1ea
S1 hiding_nonce_commitment: 022b87860b98654de610b06add7a792484ef43f31
09b25d265b911350e4e7dcf6e
S1 binding_nonce_commitment: 0329d5f8ad2b432d2fd576be4cf05fbbd37304b5
f322a869b3b6728e1f566b1d03
S1 binding_factor_input: 3617acb73b44df565fbcbbbd1824142c473ad1d6c800
7c4b72a298d1eaae576699132648562187e574a5a5c27d9b059b7b3c5c875491e2f6b
d7c34eb7e2eb6b70001
S1 binding_factor: 47122f61bf2003fc170170af030aac8cfc5f1458e1a3cec6ea
4aede8707e9fc0
S3 hiding_nonce_randomness: dfd29f2c3667052c186155084923b679858a9f9ac
e10dbadd9df48dc52ce2573
S3 binding_nonce_randomness: bb71a8a457d1a6790a148102fa2e06cbba2ae885
8e28000b2bdd0ce4b3dd58b6
S3 hiding_nonce: 83abe636c14a271b8be4de17f7897bc1ee8307f8aa10b633af96
c809964072ca
S3 binding_nonce: fc64ad877af42676c1d6f9f4b96e702930f74836a04e246d56e
bd0b902f589f2
S3 hiding_nonce_commitment: 0200db3d75d6c70bffbdd7a52e549dca170871a5e
92534568497be0b8c7d08fbf2
S3 binding_nonce_commitment: 02a0e92295f5ff637bb172a9f8c2b7d371f979a6
1ff3ae9c8da425edec419f8896
S3 binding_factor_input: 3617acb73b44df565fbcbbbd1824142c473ad1d6c800
7c4b72a298d1eaae576699132648562187e574a5a5c27d9b059b7b3c5c875491e2f6b
d7c34eb7e2eb6b70003
S3 binding_factor: 47e0feadb3f4f324bffc631022868698cdf4466aa8a4c25354
6ef4bc3f257306

// Round two parameters
participants: 1,3

// Signer round two outputs
S1 sig_share: a5f974525fce4f24790fc237bc0b6aa78904b91b0e539e034d2922e
68acb0326
S3 sig_share: a98083d8294f6cf93a68a56a82c07cb69c200005acf04564a4c7153
7d83a0295

sig: 020b9883e56ccd5b27bbe0f65670193a275d7c678f198c6a53b0704547073b1f
384f79f82b891dbc1cb37867a23ecbe75e683dbe73142c44e2fe366d5b66a1e06a
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
S1 hiding_nonce_randomness: 4bca45714e083d91f7b1ac5d55f1fdc2110e02d4c
795694e242d32f1d5cc5fb6
S1 binding_nonce_randomness: 20717c3650be9dbd9bba305ce15b248c7b63d530
e614d9db28c7b73696638695
S1 hiding_nonce: d702a4d4998dc9dec48c0b3edb4180b28498307a6ffc108419f9
f9f836c0247d
S1 binding_nonce: dda3894a479a7bcd912f87e9f566f47f1082d284e0003a22b40
96771580b2948
S1 hiding_nonce_commitment: 037e20051a2812ca588081f539a4f84dabafec183
25f24cbb3633b581100a89638
S1 binding_nonce_commitment: 02d763ba52e6484a0ddbb3d110fdc6ceb1265066
718ba8da6c14733c9e1bf28818
S1 binding_factor_input: d759fa818c284537bbb2efa2d7247eac9232b7b992cd
49237106acab251dd9548ba089a8cc7d841f6cd89ef4794837d8198bd349cf3e2c8ef
e95b4b4ddb512db0001
S1 binding_factor: 37e43476b4106e775556fca7c2fc3edf8dd02b70a10f3b3e01
6aa352177838f5
S3 hiding_nonce_randomness: 1500fcc66327aa4e08e0124ce6c867f280e118611
9a059ad59750d10dffb41fb
S3 binding_nonce_randomness: a0cf05ce7459222140088f63b1012f4a7547d1d9
23f34fdeda1f5312a0092215
S3 hiding_nonce: 81284c51df733062d12fe3582585e532336c17ecd94e9f3cf253
315b5a964c31
S3 binding_nonce: efefccd1cb6c691e20ba7ad455791bec3a91a5ca9c235892580
ad8670740e93a
S3 hiding_nonce_commitment: 02e255d43b0a2c2719edc84ad609ac7fce5d75610
6f0be92c7bb11c8530ea61994
S3 binding_nonce_commitment: 033ea6af0997848d254cb6afe8bbb870b1b8ff26
0b673486e8bc4e7eb030d64ac3
S3 binding_factor_input: d759fa818c284537bbb2efa2d7247eac9232b7b992cd
49237106acab251dd9548ba089a8cc7d841f6cd89ef4794837d8198bd349cf3e2c8ef
e95b4b4ddb512db0003
S3 binding_factor: a9fff9705c83fdc49848be9bef51784c8e774a397aff95ac65
0eacb397f97ae9

// Round two parameters
participants: 1,3

// Signer round two outputs
S1 sig_share: 1ba514cf8be3649619d5ee6d15cb9016f8c0bc2d60856aea2a744b2
6ac299598
S3 sig_share: 892b10a029afeb831b97790f0c9634ac0b2ff7c3f6e90405455b98e
e59dc1e20

sig: 036d9971d7a1ef1b27312418594a19435316ab9d8cda5f4ca8fe88c2c2cde05f
dda4d0256fb5935019356d677c2261c4c303f0b3f1576e6eef6fcfe4150605b3b8
~~~
