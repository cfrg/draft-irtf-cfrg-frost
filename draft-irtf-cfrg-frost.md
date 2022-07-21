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
key-recovery attack that is possible when even only one participant is malicious.

--- middle

# Introduction

DISCLAIMER: This is a work-in-progress draft of FROST.

RFC EDITOR: PLEASE REMOVE THE FOLLOWING PARAGRAPH The source for this draft is
maintained in GitHub. Suggested changes should be submitted as pull requests
at https://github.com/cfrg/draft-irtf-cfrg-frost. Instructions are on that page as
well.

Unlike signatures in a single-party setting, threshold signatures
require cooperation among a threshold number of signers each holding a share
of a common private key. The security of threshold schemes in general assume
that an adversary can corrupt strictly fewer than a threshold number of participants.

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

The following terminology is used throughout this document.

* A participant is an entity that is trusted to hold and use a signing key share.
* `MAX_SIGNERS` denotes the number of participants, and the number of shares that `s` is split into. This value MUST NOT exceed 2^16-1.
* `MIN_SIGNERS` denotes the threshold number of participants required to issue a signature, where MIN_SIGNERS <= MAX_SIGNERS.
* `NUM_SIGNERS` denotes the number of signers that participate in an invocation of FROST signing, where
  MIN_SIGNERS <= NUM_SIGNERS <= MAX_SIGNERS.
* An identifier is an integer value associated with a participant, or signer,
  and is a value in the range [1, MAX_SIGNERS].

Additionally, the following notation is used throughout the document.

* `encode_uint16(x)`: Convert two byte unsigned integer (uint16) `x` to a 2-byte,
  big-endian byte string. For example, `encode_uint16(310) = [0x01, 0x36]`.
* `random_bytes(n)`: Outputs `n` bytes, sampled uniformly at random
using a cryptographically secure pseudorandom number generator (CSPRNG).
* `len(l)`: Outputs the length of input list `l`, e.g., `len([1,2,3]) = 3)`.
* `reverse(l)`: Outputs the list `l` in reverse order, e.g., `reverse([1,2,3]) = [3,2,1]`.
* `range(a, b)`: Outputs a list of integers from `a` to `b-1` in ascending order, e.g., `range(1, 4) = [1,2,3]`.
* `pow(a, b)`: Output the integer result of `a` to the power of `b`, e.g., `pow(2, 3) = 8`.
* \|\| denotes concatenation, i.e., x \|\| y = xy.
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
subtraction, e.g., `A - B = A + (-B)`. Scalar multiplication is equivalent to the repeated
application of the group operation on an element A with itself `r-1` times, this is denoted
as `r*A = A + ... + A`. For any element `A`, `p * A = I`. We denote `B` as a fixed generator
of the group. Scalar base multiplication is equivalent to the repeated application of the group
operation `B` with itself `r-1` times, this is denoted as `ScalarBaseMult(r)`. The set of
scalars corresponds to `GF(p)`, which we refer to as the scalar field. This document uses types
`Element` and `Scalar` to denote elements of the group `G` and its set of scalars, respectively.
We denote equality comparison as `==` and assignment of values by `=`.

We now detail a number of member functions that can be invoked on `G`.

- Order(): Outputs the order of `G` (i.e. `p`).
- Identity(): Outputs the identity `Element` of the group (i.e. `I`).
- RandomScalar(): Outputs a random `Scalar` element in GF(p).
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

# Helper functions {#helpers}

Beyond the core dependencies, the protocol in this document depends on the
following helper operations:

- Nonce generation, {{dep-nonces}}
- Polynomial operations, {{dep-polynomial}};
- Encoding operations, {{dep-encoding}};
- Signature binding {{dep-binding-factor}}, group commitment {{dep-group-commit}}, and challenge computation {{dep-sig-challenge}}

These sections describes these operations in more detail.

## Nonce generation {#dep-nonces}

To hedge against a bad RNG that outputs predictable values, we generate
nonces by sourcing fresh randomness and combine with the secret key,
to create a domain-separated hash function from the ciphersuite hash
function `H`, `H4`:

~~~
  nonce_generate(secret):

  Inputs:
  - secret, a Scalar

  Outputs: nonce, a Scalar

  def nonce_generate(secret):
    k_enc = random_bytes(32)
    secret_enc = G.SerializeScalar(secret)
    return H3(k_enc || secret_enc)
~~~

## Polynomial Operations {#dep-polynomial}

This section describes operations on and associated with polynomials over Scalars
that are used in the main signing protocol. A polynomial of maximum degree t
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
  - "invalid parameters", if any x-coordinate is equal to 0 or if x_i
    is not in L

  def derive_lagrange_coefficient(x_i, L):
    if x_i == 0:
      raise "invalid parameters"
    for x_j in L:
      if x_j == 0:
        raise "invalid parameters"
    if x_i not in L:
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

### Deriving the constant term of a polynomial

Secret sharing requires "splitting" a secret, which is represented as
a constant term of some polynomial `f` of degree `t-1`. Recovering the
constant term occurs with a set of `t` points using polynomial
interpolation, defined as follows.

~~~
  Inputs:
  - points, a set of t points on a polynomial f, each a tuple of two
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
      encoded_commitment = encode_uint16(identifier) ||
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
    a list of commitments issued by each signer, where each element in the list
    indicates the signer identifier i and their two commitment Element values
    (hiding_nonce_commitment_i, binding_nonce_commitment_i). This list MUST be sorted
    in ascending order by signer identifier.

  Outputs: A list of signer participant identifiers

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
    a list of binding factors for each signer, where each element in the list
    indicates the signer identifier i and their binding factor. This list MUST be sorted
    in ascending order by signer identifier.
  - identifier, Identifier i of the signer.

  Outputs: A Scalar value.

  Errors: "invalid participant", when the designated participant is not known

def binding_factor_for_participant(binding_factor_list, identifier):
  binding_factors = []
  for (i, binding_factor) in commitment_list:
    if identifier == i:
      return binding_factor
  raise "invalid participant"
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
      rho_input = rho_input_prefix || encode_uint16(identifier)
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
      binding_factor = binding_factor_for_participant(binding_factors, identifier)
      group_commitment = group_commitment +
        (hiding_nonce_commitment + (binding_factor * binding_nonce_commitment))
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

We now present the two-round variant of the FROST threshold signature protocol for producing Schnorr signatures.
It involves signer participants and a Coordinator. Signer participants are
entities with signing key shares that participate in the threshold signing
protocol. The Coordinator is an entity with the following responsibilities:

1. Determining which signers will participate (at least MIN_SIGNERS in number);
2. Coordinating rounds (receiving and forwarding inputs among participants); and
3. Aggregating signature shares output by each participant, and publishing the resulting signature.

FROST assumes the selection of all participants, including Coordinator and set of
signers, are all chosen external to the protocol. Note that it is possible to
deploy the protocol without a distinguished Coordinator; see {{no-coordinator}}
for more information.

Because key generation is not specified, all signers are assumed to have the (public) group state that we refer to as "group info"
below, and their corresponding signing key shares.

In particular, it is assumed that the Coordinator and each signer participant `P_i` knows the following
group info:

- Group public key, an `Element` in `G`, denoted `PK`, corresponding
  to the group secret key `s`, which is a `Scalar`. `PK` is an output from the group's key generation protocol, such as `trusted_dealer_keygen` or a DKG.
- Public keys for each signer, denoted `PK_i`, which are similarly outputs
  from the group's key generation protocol, `Element` values in `G`.

And that each participant with identifier `i` additionally knows the following:

- Participant `i`s signing key share `sk_i`, which is the i-th secret share of `s`, a `Scalar`.

By construction, `PK = G.ScalarBaseMult(s)` and `PK_i = G.ScalarMultBase(sk_i)` for each participant `i`.

The exact key generation mechanism is out of scope for this specification. In general,
key generation is a protocol that outputs (1) a shared, group public key PK owned
by each Signer, and (2) individual shares of the signing key owned by each Signer.
In general, two possible key generation mechanisms are possible, one that requires
a single, trusted dealer, and the other which requires performing a distributed
key generation protocol. We highlight key generation mechanism by a trusted dealer
in {{dep-dealer}}, for reference.

This signing variant of FROST requires signers to perform two network rounds:
1) generating and publishing commitments, and 2) signature share generation and
publication. The first round serves for each participant to issue a commitment to
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
            |    signer commitment                     |
            |<-----------------------------------------+

      == Round 2 (Signature Share Generation) ==
            |
            |     signer input       |                 |
            +------------------------>                 |
            |     signature share    |                 |
            |<-----------------------+                 |
            |          ...                             |
            |     signer input                         |
            +------------------------------------------>
            |     signature share                      |
            <------------------------------------------+
            |
      == Aggregation ==
            |
  signature |
<-----------+
~~~
{: #fig-frost title="FROST signature overview" }

Details for round one are described in {{frost-round-one}}, and details for round two
are described in {{frost-round-two}}. The final Aggregation step is described in
{{frost-aggregation}}.

FROST assumes that all inputs to each round, especially those of which are received
over the network, are validated before use. In particular, this means that any value
of type Element or Scalar is deserialized using DeserializeElement and DeserializeScalar,
respectively, as these functions perform the necessary input validation steps.

FROST assumes reliable message delivery between the Coordinator and signer participants in
order for the protocol to complete. An attacker masquerading as another participant
will result only in an invalid signature; see {{sec-considerations}}. However, in order
to identify any participant which has misbehaved (resulting in the protocol aborting)
to take actions such as excluding them from future signing operations, we assume that
the network channel is additionally authenticated; confidentiality is not required.

## Round One - Commitment {#frost-round-one}

Round one involves each signer generating nonces and their corresponding public commitments.
A nonce is a pair of Scalar values, and a commitment is a pair of Element values.

Each signer in round one generates a nonce `nonce = (hiding_nonce, binding_nonce)` and commitment
`comm = (hiding_nonce_commitment, binding_nonce_commitment)`.

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

The private output `nonce` from Participant `P_i` is stored locally and kept private
for use in the second round. This nonce MUST NOT be reused in more than one invocation
of FROST, and it MUST be generated from a source of secure randomness. The public output
`comm` from Participant `P_i` is sent to the Coordinator.

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
MUST abort the protocol. Moreover, each signer MUST ensure that their identifier as well as their commitment as from the first round appears in commitment_list.
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

The output of this procedure is a signature share. Each signer then sends
these shares back to the Coordinator. Each signer MUST delete the nonce and
corresponding commitment after this round completes, and MUST use the nonce to generate at most one
signature share.

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
    binding_factor = binding_factor_for_participant(binding_factor_list, identifier)

    # Compute the group commitment
    group_commitment = compute_group_commitment(commitment_list, binding_factor_list)

    # Compute the commitment share
    (hiding_nonce_commitment, binding_nonce_commitment) = comm_i
    comm_share = hiding_nonce_commitment + (binding_nonce_commitment * binding_factor)

    # Compute the challenge
    challenge = compute_challenge(group_commitment, group_public_key, msg)

    # Compute Lagrange coefficient
    participant_list = participants_from_commitment_list(commitment_list)
    lambda_i = derive_lagrange_coefficient(identifier, participant_list)

    # Compute relation values
    l = G.ScalarBaseMult(sig_share_i)
    r = comm_share + ((challenge * lambda_i) * PK_i)

    return l == r
~~~

If any signature share fails to verify, i.e., if verify_signature_share returns False for
any signer share, the Coordinator MUST abort the protocol for correctness reasons.
Excluding one signer means that their nonce will not be included in the joint response `z`
and consequently the output signature will not verify.

Otherwise, if all signer shares are valid, the Coordinator performs the `aggregate` operation
and publishes the resulting signature.

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
  - Order: 2^252 + 27742317777372353535851937790883648493 (see {{?RFC7748}})
  - Identity: As defined in {{RFC7748}}.
  - RandomScalar: Implemented by repeatedly generating a random 32-byte string
    and invoking DeserializeScalar on the result until success.
  - SerializeElement: Implemented as specified in {{!RFC8032, Section 5.1.2}}.
  - DeserializeElement: Implemented as specified in {{!RFC8032, Section 5.1.3}}.
    Additionally, this function validates that the resulting element is not the group
    identity element and is in the prime-order subgroup. The latter check can
    be implemented by multiplying the resulting point by the order of the group and
    checking that the result is the identity element.
  - SerializeScalar: Implemented by outputting the little-endian 32-byte encoding of
    the Scalar value.
  - DeserializeScalar: Implemented by attempting to deserialize a Scalar from a 32-byte
    string. This function can fail if the input does not represent a Scalar between
    the value 0 and `G.Order() - 1`.

- Hash (`H`): SHA-512, and Nh = 64.
  - H1(m): Implemented by computing H("rho" || m), interpreting the 64-byte digest
    as a little-endian integer, and reducing the resulting integer modulo
    L = 2^252+27742317777372353535851937790883648493.
  - H2(m): Implemented by computing H(m), interpreting the 64-byte digest
    as a little-endian integer, and reducing the resulting integer modulo
    L = 2^252+27742317777372353535851937790883648493.
  - H3(m): Implemented by computing H("nonce" || m), interpreting the 64-byte digest
    as a little-endian integer, and reducing the resulting integer modulo
    L = 2^252+27742317777372353535851937790883648493.
  - H4(m): Implemented by computing H(contextString \|\| "msg" \|\| m).
  - H5(m): Implemented by computing H(contextString \|\| "com" \|\| m).


Normally H2 would also include a domain separator, but for backwards compatibility
with {{!RFC8032}}, it is omitted.

Signature verification is as specified in {{Section 5.1.7 of RFC8032}} with the
constraint that implementations MUST check the group group equation [8][S]B = [8]R + [8][k]A'.
The alternative check [S]B = R + [k]A' is not safe or interoperable in practice.

## FROST(ristretto255, SHA-512) {#recommended-suite}

This ciphersuite uses ristretto255 for the Group and SHA-512 for the Hash function `H`.
The value of the contextString parameter is "FROST-RISTRETTO255-SHA512-v8".

- Group: ristretto255 {{!RISTRETTO=I-D.irtf-cfrg-ristretto255-decaf448}}
  - Order: 2^252 + 27742317777372353535851937790883648493 (see {{RISTRETTO}})
  - Identity: As defined in {{RISTRETTO}}.
  - RandomScalar: Implemented by repeatedly generating a random 32-byte string and
    invoking DeserializeScalar on the result until success.
  - SerializeElement: Implemented using the 'Encode' function from {{!RISTRETTO}}.
  - DeserializeElement: Implemented using the 'Decode' function from {{!RISTRETTO}}.
  - SerializeScalar: Implemented by outputting the little-endian 32-byte encoding of
    the Scalar value.
  - DeserializeScalar: Implemented by attempting to deserialize a Scalar from a 32-byte
    string. This function can fail if the input does not represent a Scalar between
    the value 0 and `G.Order() - 1`.

- Hash (`H`): SHA-512, and Nh = 64.
  - H1(m): Implemented by computing H(contextString || "rho" || m) and mapping the
    output to a Scalar as described in {{!RISTRETTO, Section 4.4}}.
  - H2(m): Implemented by computing H(contextString || "chal" || m) and mapping the
    output to a Scalar as described in {{!RISTRETTO, Section 4.4}}.
  - H3(m): Implemented by computing H(contextString || "nonce" || m) and mapping the
    output to a Scalar as described in {{!RISTRETTO, Section 4.4}}.
  - H4(m): Implemented by computing H(contextString \|\| "msg" \|\| m).
  - H5(m): Implemented by computing H(contextString \|\| "com" \|\| m).

Signature verification is as specified in {{prime-order-verify}}.

## FROST(Ed448, SHAKE256)

This ciphersuite uses edwards448 for the Group and SHAKE256 for the Hash function `H`
meant to produce signatures indistinguishable from Ed448 as specified in {{!RFC8032}}.
The value of the contextString parameter is "FROST-ED448-SHAKE256-v8".

- Group: edwards448 {{!RFC8032}}
  - Order: 2^446 - 13818066809895115352007386748515426880336692474882178609894547503885
  - Identity: As defined in {{RFC7748}}.
  - RandomScalar: Implemented by repeatedly generating a random 48-byte string and
    invoking DeserializeScalar on the result until success.
  - SerializeElement: Implemented as specified in {{!RFC8032, Section 5.2.2}}.
  - DeserializeElement: Implemented as specified in {{!RFC8032, Section 5.2.3}}.
    Additionally, this function validates that the resulting element is not the group
    identity element.
  - SerializeScalar: Implemented by outputting the little-endian 48-byte encoding of
    the Scalar value.
  - DeserializeScalar: Implemented by attempting to deserialize a Scalar from a 48-byte
    string. This function can fail if the input does not represent a Scalar between
    the value 0 and `G.Order() - 1`.

- Hash (`H`): SHAKE256, and Nh = 114.
  - H1(m): Implemented by computing H("rho" || m), interpreting the lower
    57 bytes as a little-endian integer, and reducing the resulting integer modulo
    L = 2^446 - 13818066809895115352007386748515426880336692474882178609894547503885.
  - H2(m): Implemented by computing H(m), interpreting the lower 57 bytes
    as a little-endian integer, and reducing the resulting integer modulo
    L = 2^446 - 13818066809895115352007386748515426880336692474882178609894547503885.
  - H3(m): Implemented by computing H("nonce" || m), interpreting the lower
    57 bytes as a little-endian integer, and reducing the resulting integer modulo
    L = 2^446 - 13818066809895115352007386748515426880336692474882178609894547503885.
  - H4(m): Implemented by computing H(contextString \|\| "msg" \|\| m).
  - H5(m): Implemented by computing H(contextString \|\| "com" \|\| m).

Normally H2 would also include a domain separator, but for backwards compatibility
with {{!RFC8032}}, it is omitted.

Signature verification is as specified in {{Section 5.2.7 of RFC8032}} with the
constraint that implementations MUST check the group group equation [4][S]B = [4]R + [4][k]A'.
The alternative check [S]B = R + [k]A' is not safe or interoperable in practice.

## FROST(P-256, SHA-256)

This ciphersuite uses P-256 for the Group and SHA-256 for the Hash function `H`.
The value of the contextString parameter is "FROST-P256-SHA256-v8".

- Group: P-256 (secp256r1) {{x9.62}}
  - Order: 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
  - Identity: As defined in {{x9.62}}.
  - RandomScalar: Implemented by repeatedly generating a random 32-byte string
    and invoking DeserializeScalar on the result until success.
  - SerializeElement: Implemented using the compressed Elliptic-Curve-Point-to-Octet-String
    method according to {{SECG}}.
  - DeserializeElement: Implemented by attempting to deserialize a public key using
    the compressed Octet-String-to-Elliptic-Curve-Point method according to {{SECG}},
    and then performs partial public-key validation as defined in section 5.6.2.3.4 of
    {{!KEYAGREEMENT=DOI.10.6028/NIST.SP.800-56Ar3}}. This includes checking that the
    coordinates of the resulting point are in the correct range, that the point is on
    the curve, and that the point is not the point at infinity. Additionally, this function
    validates that the resulting element is not the group identity element.
    If these checks fail, deserialization returns an error.
  - SerializeScalar: Implemented using the Field-Element-to-Octet-String conversion
    according to {{SECG}}.
  - DeserializeScalar: Implemented by attempting to deserialize a Scalar from a 32-byte
    string using Octet-String-to-Field-Element from {{SECG}}. This function can fail if the
    input does not represent a Scalar between the value 0 and `G.Order() - 1`.

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
the protocol, although participants still are able to verify the consistency of their
shares via a VSS (verifiable secret sharing) step; see {{dep-vss}}.

* Unforgeability assuming at most `(MIN_SIGNERS-1)` corrupted signers. So long as an adversary
corrupts fewer than `MIN_SIGNERS` participants, the scheme remains secure against Existential
Unforgeability Under Chosen Message Attack (EUF-CMA) attacks, as defined in {{BonehShoup}},
Definition 13.2.

* Coordinator. We assume the Coordinator at the time of signing does not perform a
denial of service attack. A denial of service would include any action which either
prevents the protocol from completing or causing the resulting signature to be invalid.
Such actions for the latter include sending inconsistent values to signer participants,
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

Nonces generated by each participant in the first round of signing must be sampled
uniformly at random and cannot be derived from some deterministic function. This
is to avoid replay attacks initiated by other signers, which allows for a complete
key-recovery attack. The Coordinator MAY further hedge against nonce reuse attacks by
tracking signer nonce commitments used for a given group key, at the cost of additional
state.

## Protocol Failures

We do not specify what implementations should do when the protocol fails, other than requiring that
the protocol abort. Examples of viable failure include when a verification check returns invalid or
if the underlying transport failed to deliver the required messages.

## Removing the Coordinator Role {#no-coordinator}

In some settings, it may be desirable to omit the role of the Coordinator entirely.
Doing so does not change the security implications of FROST, but instead simply
requires each participant to communicate with all other participants. We loosely
describe how to perform FROST signing among signers without this coordinator role.
We assume that every participant receives as input from an external source the
message to be signed prior to performing the protocol.

Every participant begins by performing `commit()` as is done in the setting
where a Coordinator is used. However, instead of sending the commitment
to the Coordinator, every participant instead will publish
this commitment to every other participant. Then, in the second round, signers will already have
sufficient information to perform signing. They will directly perform `sign`.
All participants will then publish their signature shares to one another. After having
received all signature shares from all other signers, each signer will then perform
`verify_signature_share` and then `aggregate` directly.

The requirements for the underlying network channel remain the same in the setting
where all participants play the role of the Coordinator, in that all messages that
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

* Isis Lovecruft
* T. Wilson-Brown
* Alden Torres

--- back

# Acknowledgments

This document was improved based on input and contributions by the Zcash Foundation engineering team.

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
    r = R + (c * PK)
    return l == r
~~~

# Trusted Dealer Key Generation {#dep-dealer}

One possible key generation mechanism is to depend on a trusted dealer, wherein the
dealer generates a group secret `s` uniformly at random and uses Shamir and Verifiable
Secret Sharing as described in {{dep-shamir}} and {{dep-vss}} to create secret
shares of `s` to be sent to all other participants. We highlight at a high level how this
operation can be performed.

The dealer is trusted to 1) generate good randomness, and 2) delete secret values after distributing shares to each participant,
and 3) keep secret values confidential.

~~~
  Inputs:
  - s, a group secret, Scalar, that MUST be derived from at least Ns bytes of entropy
  - MAX_SIGNERS, the number of shares to generate, an integer
  - MIN_SIGNERS, the threshold of the secret sharing scheme, an integer

  Outputs:
  - signer_private_keys, MAX_SIGNERS shares of the secret key s, each a Scalar value.
  - vss_commitment, a vector commitment of Elements in G, to each of the coefficients
    in the polynomial defined by secret_key_shares and whose first element is
    G.ScalarBaseMult(s).

  def trusted_dealer_keygen(s, MAX_SIGNERS, MIN_SIGNERS):
    signer_private_keys, coefficients = secret_share_shard(secret_key, MAX_SIGNERS, MIN_SIGNERS)
    vss_commitment = vss_commit(coefficients):
    PK = G.ScalarBaseMult(secret_key)
    return signer_private_keys, vss_commitment
~~~

It is assumed the dealer then sends one secret key share to each of the NUM_SIGNERS participants, along with `vss_commitment`.
After receiving their secret key share and `vss_commitment`, participants MUST abort if they do not have the same view of `vss_commitment`.
Otherwise, each participant MUST perform `vss_verify(secret_key_share_i, vss_commitment)`, and abort if the check fails.
The trusted dealer MUST delete the secret_key and secret_key_shares upon completion.

Use of this method for key generation requires a mutually authenticated secure channel
between the dealer and participants to send secret key shares, wherein the channel provides confidentiality
and integrity. Mutually authenticated TLS is one possible deployment option.

## Shamir Secret Sharing {#dep-shamir}

In Shamir secret sharing, a dealer distributes a secret `Scalar` `s` to `n` participants
in such a way that any cooperating subset of `MIN_SIGNERS` participants can recover the
secret. There are two basic steps in this scheme: (1) splitting a secret into
multiple shares, and (2) combining shares to reveal the resulting secret.

This secret sharing scheme works over any field `F`. In this specification, `F` is
the scalar field of the prime-order group `G`.

The procedure for splitting a secret into shares is as follows.

~~~
  secret_share_shard(s, MAX_SIGNERS, MIN_SIGNERS):

  Inputs:
  - s, secret value to be shared, a Scalar
  - MAX_SIGNERS, the number of shares to generate, an integer
  - MIN_SIGNERS, the threshold of the secret sharing scheme, an integer

  Outputs:
  - secret_key_shares, A list of MAX_SIGNERS number of secret shares, which is a tuple
    consisting of the participant identifier and the key share, each of which is a Scalar
  - coefficients, a vector of the t coefficients which uniquely determine
    a polynomial f.

  Errors:
  - "invalid parameters", if MIN_SIGNERS > MAX_SIGNERS or if MIN_SIGNERS is less than 2

  def secret_share_shard(s, MAX_SIGNERS, MIN_SIGNERS):
    if MIN_SIGNERS > MAX_SIGNERS:
      raise "invalid parameters"
    if MIN_SIGNERS < 2:
      raise "invalid parameters"

    # Generate random coefficients for the polynomial, yielding
    # a polynomial of degree (MIN_SIGNERS - 1)
    coefficients = [s]
    for i in range(1, MIN_SIGNERS):
      coefficients.append(G.RandomScalar())

    # Evaluate the polynomial for each point x=1,...,n
    secret_key_shares = []
    for x_i in range(1, MAX_SIGNERS + 1):
      y_i = polynomial_evaluate(x_i, coefficients)
      secret_key_share_i = (x_i, y_i)
      secret_key_share.append(secret_key_share_i)
    return secret_key_shares, coefficients
~~~

Let `points` be the output of this function. The i-th element in `points` is
the share for the i-th participant, which is the randomly generated polynomial
evaluated at coordinate `i`. We denote a secret share as the tuple `(i, points[i])`,
and the list of these shares as `shares`.
`i` MUST never equal `0`; recall that `f(0) = s`, where `f` is the polynomial defined in a Shamir secret sharing operation.

The procedure for combining a `shares` list of length `MIN_SIGNERS` to recover the
secret `s` is as follows.

~~~
  secret_share_combine(shares):

  Inputs:
  - shares, a list of at minimum MIN_SIGNERS secret shares, each a tuple (i, f(i))

  Outputs: The resulting secret s, a Scalar, that was previously split into shares

  Errors:
  - "invalid parameters", if less than MIN_SIGNERS input shares are provided

  def secret_share_combine(shares):
    if len(shares) < MIN_SIGNERS:
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
the correct secret.

The procedure for committing to a polynomial `f` of degree `MIN_SIGNERS-1` is as follows.

~~~
  vss_commit(coeffs):

  Inputs:
  - coeffs, a vector of the MIN_SIGNERS coefficients which uniquely determine
  a polynomial f.

  Outputs: a commitment vss_commitment, which is a vector commitment to each of the
  coefficients in coeffs, where each element of the vector commitment is an `Element` in `G`.

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

  vss_verify(share_i, commitment)
    (i, sk_i) = share_i
    S_i = ScalarBaseMult(sk_i)
    S_i' = G.Identity()
    for j in range(0, MIN_SIGNERS):
      S_i' += pow(i, j) * vss_commitment[j]
    if S_i == S_i':
      return 1
    return 0
~~~

We now define how the Coordinator and signer participants can derive group info,
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
      where each PK_i is the public key, an Element, for participant i.

    derive_group_info(MAX_SIGNERS, MIN_SIGNERS, vss_commitment)
      PK = vss_commitment[0]
      signer_public_keys = []
      for i in range(1, MAX_SIGNERS+1):
        PK_i = G.Identity()
        for j in range(0, MIN_SIGNERS):
          PK_i += pow(i, j) * vss_commitment[j]
        signer_public_keys.append(PK_i)
      return PK, signer_public_keys
~~~

# Test Vectors

This section contains test vectors for all ciphersuites listed in {{ciphersuites}}.
All `Element` and `Scalar` values are represented in serialized form and encoded in
hexadecimal strings. Signatures are represented as the concatenation of their
constituent parts. The input message to be signed is also encoded as a hexadecimal
string.

Each test vector consists of the following information.

- Configuration: This lists the fixed parameters for the particular instantiation
  of FROST, including MAX_SIGNERS, MIN_SIGNERS, and NUM_SIGNERS.
- Group input parameters: This lists the group secret key and shared public key,
  generated by a trusted dealer as described in {{dep-dealer}}, as well as the
  input message to be signed. All values are encoded as hexadecimal strings.
- Signer input parameters: This lists the signing key share for each of the
  NUM_SIGNERS signers.
- Round one parameters and outputs: This lists the NUM_SIGNERS participants engaged
  in the protocol, identified by their integer identifier, the hiding and binding commitment
  values produced in {{frost-round-one}}, as well as the resulting group binding factor input,
  computed in part from the group commitment list encoded as described in {{dep-encoding}},
  and group binding factor as computed in {{frost-round-two}}).
- Round two parameters and outputs: This lists the NUM_SIGNERS participants engaged
  in the protocol, identified by their integer identifier, along with their corresponding
  output signature share as produced in {{frost-round-two}}.
- Final output: This lists the aggregate signature as produced in {{frost-aggregation}}.


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
S1 hiding_nonce: d9aad97e1a1127bb87702ce8d81d8c07c7cbca89e784868d8e38
76ff6b459700
S1 binding_nonce: 5063be2774520d08a5ccd7f1213fb1179a5fa292bf13bc91cb2
8e7bd4d4a690c
S1 hiding_nonce_commitment: 33fc1eacb8d168e54ab811320196b7715a9918461
e1e00c3688e503ace1628d5
S1 binding_nonce_commitment: b32d41ce5a230b459de8c49b0619cb5fbde46690
752ec94ef05aa1f8647301df
S1 binding_factor_input: ee26b0dd4af7e749aa1a8ee3c10ae9923f618980772e
473f8819a5d4940e0db27ac185f8a0e1d5f84f88bc887fd67b143732c304cc5fa9ad8
e6f57f50028a8ff7b5e7b0a8efad964ba83310b56607920b6c3c979e38e583aa9d02a
df541c58ea92a259b5c8a184d0a7c5ea978e42a8ff84608c38cbb22475bd54858c4ff
d524e0001
S1 binding_factor: a523eba59830d1b5dbe6914e954862c5396b979bcd258fe323
e324335db81101
S3 hiding_nonce: 86961f3a429ac0c5696f49e6d796817ff653f83c07f34e9e1f4d
4c8c515b7900
S3 binding_nonce: 72225ec11c1315d9f1ea0e78b1160ed95800fadd0191d23fd2f
2c90ac96cb307
S3 hiding_nonce_commitment: 493651312d26af93d2bc5b92eeecc12f1d6da9e18
4911e0943ebeb5ec59d3926
S3 binding_nonce_commitment: 8dae85381a582288c934741defbcaeba7a1b944e
3a2df0aa0ac96aec4431c690
S3 binding_factor_input: ee26b0dd4af7e749aa1a8ee3c10ae9923f618980772e
473f8819a5d4940e0db27ac185f8a0e1d5f84f88bc887fd67b143732c304cc5fa9ad8
e6f57f50028a8ff7b5e7b0a8efad964ba83310b56607920b6c3c979e38e583aa9d02a
df541c58ea92a259b5c8a184d0a7c5ea978e42a8ff84608c38cbb22475bd54858c4ff
d524e0003
S3 binding_factor: c900ec81622c4b4b756139607357c1bf531df1a3b055304af2
15278aadb84b02

// Round two parameters
participants: 1,3

// Signer round two outputs
S1 sig_share: caae171b83bff0c2c6f56a1276892918ba228146f6344b85d2ec6ef
eb6f16d0d
S3 sig_share: ea6fdbf61683cf5f1f742e1b91583f0f667f0369efd2e33399b96d5
a3ff0300d

sig: 5da10008c13c04dd72328ba8e0f72b63cad43c3bf4b7eaada1c78225afbd977e
c74afdb47fdfadca0fcda18a28e8891220a284afe5072fb96ba6dc58f6e19e0a
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
group_public_key: 1588564c56a8edb53b55399df5b65fd2abe777717baa2ef440b
13fe13b7ce077347f5e4346ab4475f9258fb947978b0123884832a46c6be800
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
S1 hiding_nonce: a7fa56e3dc9935845e58275131eeda30d648432cba7ec3e3c522
dea613962439cdbd016cd78d54eb72ba8ec4e1b4e6cb41d3afb55a28f40300
S1 binding_nonce: 66480d4125faf4033babeee514f0b8d26118618ad05d6e3f8e6
4ea7082249b460c9eee5259f6ca6d1036db968923a89534b679c6ec96181b00
S1 hiding_nonce_commitment: b4b449e692a233b7661da0dbe4c337dd1c8c8369f
c0786d6d1537ab371bb8afc4e59812de18300aef79b26920696c180e2f78f96bfb0d9
1100
S1 binding_nonce_commitment: 705e18f4f601754c700ef93591fb24af5d3ca0c8
052a890de5aa2dc9231903b5d0d8a56c0dfe5b3c66e94b8615f705e7a5086fe93c020
b5600
S1 binding_factor_input: b54ff7255705a71ee2925e4a3e30e41aed489a579d55
95e0df13e32e1e4dd202a7c7f68b31d6418d9845eb4d757adda6ab189e1bb340db818
e5b3bc725d992faf63e9b0500db10517fe09d3f566fba3a80e46a403e0c7d41548fbf
75cf2662b00225b502961f98d8c9ff937de0b24c231845c16de964d8b11ffe861c657
afc6656a15d98dc9e6df3d2371d0fd2e0d990ad977470d0a371c1510accd90bb9fe51
4da13c4c2d97488a7980cb7ea47ac5124ec710faa8692c009794b7c7a9e29b8cc5ea4
cd9418c853676e55971349c313f84b902c1a112a0ecdbecb5fb6030ad874161ff7c00
01
S1 binding_factor: 63e240eeaa6d10b99561d7eb813fd4164f3cde8eeffcf2c973
c9de583ea075e471efbeb949af4fb11e7659bfacbd67eba4d9aa58c653190f00
S3 hiding_nonce: 6341f043b08f518d5f12ce4d699e3827e0ad7a8f2a4bcdcee64f
afe99dfbbe4187a01ebdf967a3503bbd84af24e0af93b078ab8d1cda533c00
S3 binding_nonce: 1716d9dc1e4c97553708f2ebc65039a50d00919a68940afd660
f31d1939e6e5f4a88631693f1acb2e737feff2bef7b0cdb1d3baae603272900
S3 hiding_nonce_commitment: 8dd1e8cf1e0330bbcdeced3e8e325e48bba2b0caf
34185a53bd8227f1c96be778681164417a582d39f1bea23a8dfe5a9e0a96d3dbbf8ee
6180
S3 binding_nonce_commitment: 58df1966884f46af333e26b6c1cace2720e2bd70
39a21b1b8483e28974237bcea8c5649cfe460e821afc94021d0b686029681a1148cd3
f0e00
S3 binding_factor_input: b54ff7255705a71ee2925e4a3e30e41aed489a579d55
95e0df13e32e1e4dd202a7c7f68b31d6418d9845eb4d757adda6ab189e1bb340db818
e5b3bc725d992faf63e9b0500db10517fe09d3f566fba3a80e46a403e0c7d41548fbf
75cf2662b00225b502961f98d8c9ff937de0b24c231845c16de964d8b11ffe861c657
afc6656a15d98dc9e6df3d2371d0fd2e0d990ad977470d0a371c1510accd90bb9fe51
4da13c4c2d97488a7980cb7ea47ac5124ec710faa8692c009794b7c7a9e29b8cc5ea4
cd9418c853676e55971349c313f84b902c1a112a0ecdbecb5fb6030ad874161ff7c00
03
S3 binding_factor: bb8b3d669199e180628a91097a03422c12103b2f34c7931f98
0accb20574a506d8cf966c444fcf5fd5bbfbc6943440aa981ef6fb070fad0600

// Round two parameters
participants: 1,3

// Signer round two outputs
S1 sig_share: a2697f5e866a4b61651f16df4105b80a47365294522dbfa26ed9f8b
cb66954dec45326f5645590f2e0a8664e8870c053ec8ba5a58526a42f00
S3 sig_share: 1bce211bc3a8ccd27721c091bc426f422314f70b0bde3f4c45bfad2
48e57643f68983bcba53e6c500bbb4d19de4b5320e44a757c8997042c00

sig: 60cf90055083501d04f38c133c01f121444a6c6889745363555cea964285d5eb
bdb25690cdff9ca96a28b10bab68aa721b0fca9288a7efbe80caf248ceb6509f1088b
110e38b85ba2bda1373f11330b02aca74dc6445c1b81d2dec61c00a94fc42ec63b467
66bc1374d0d61a220fbea81b00
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
S1 hiding_nonce: eb0dc12ae7b746d36e3f2de46ce3833a05b9d4af5434eeb8cafa
efda76906d00
S1 binding_nonce: 491e91aa9df514ef598d5e0c7c5cdd088fbde4965b96069d546
c0f04f1822b03
S1 hiding_nonce_commitment: c6fe28df6a13f2ea80a911dd7a284e4b185bc8d3e
3102adaf88807a5e3d3813c
S1 binding_nonce_commitment: a413722bcfc71ba044bb2846b814401e60fed6b2
fc5bfb25f5a49e63474b7011
S1 binding_factor_input: 678630bf982c566949d7f22d2aefb94f252c664216d3
32f34e2c8fdcd7045f207f854504d0daa534a5b31dbdf4183be30eb4fdba4f962d8a6
b69cf20c2734043c229faa47541463641bcc7c23a4576d74e536dea0d7f7ae6e2c846
1a63f4fe97599d8d83005d520a104f937ce3b8181281348fad246e1c0d89ed4cca7d5
22e750001
S1 binding_factor: 2e81f15e28874f517b6d2023291e49000f71f998852b484aae
f945000478ea05
S3 hiding_nonce: abd12b8e6f255ee1e540eab029003a6e956567617720f61115f0
941615892209
S3 binding_nonce: 218e22625f93f262f025bd2d13c46ba722aa29fe585ceed66ff
442d98fe4e509
S3 hiding_nonce_commitment: 5450c4c98c3fc6bb579bded17fcdc23073d2ecfb7
61e3f9433cbc991e1496068
S3 binding_nonce_commitment: 0ae0cf608fcba285ec1f6c84c955572c91a4fafc
c1f1120f4f30b25e40fbcc0a
S3 binding_factor_input: 678630bf982c566949d7f22d2aefb94f252c664216d3
32f34e2c8fdcd7045f207f854504d0daa534a5b31dbdf4183be30eb4fdba4f962d8a6
b69cf20c2734043c229faa47541463641bcc7c23a4576d74e536dea0d7f7ae6e2c846
1a63f4fe97599d8d83005d520a104f937ce3b8181281348fad246e1c0d89ed4cca7d5
22e750003
S3 binding_factor: 240d5257c68e377c1994481081a8a4c4362b9e82e523088c30
d91f8c2811890e

// Round two parameters
participants: 1,3

// Signer round two outputs
S1 sig_share: efae3a83437fa8cd96194aacc56a7eb841630c280da99e7764a81d1
340323306
S3 sig_share: 96ddc4582e45eabce46f07b9e9375f8b49d35d1510fd34ac02b1e79
d6100a602

sig: 7ec584cef9a383afb43883b73bcaa6313afe878bd5fe75a608311b866a76ec67
858cffdb71c4928a7b895165afa2dd438b366a3d1da6d323675905b1a132d908
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
S1 hiding_nonce: 33a519cf070a166f9ef41a798d03423743f3e7d0b0efd5d0d963
773c4c53205e
S1 binding_nonce: 307d208d0c5728f323ae374f1ebd7f14a1a49b77d9d4bc1eab2
22218a17765ff
S1 hiding_nonce_commitment: 021e5c8b286dc859314eb1c0a2024a2077ad49b60
3112dd7bfaf326591d3fab332
S1 binding_nonce_commitment: 039431f230cf2bd90ad556a7f3d6b5a5686efd19
4c863356628d7296c2a3fa5900
S1 binding_factor_input: 7a753fed12531fbcd151e1d84702927c39063e780e91
c01f02bd11b60d7632bf44df5a9e0d49f359549018a13a586b5ede02cadef80472f75
d195b82160f43ea0001
S1 binding_factor: 71f09a2c4a1fc2f7a1379102809b4ac3247837c532cc5cf091
3782496c515655
S3 hiding_nonce: a614eadb972dc37b88aeceb6e899903f3104742d13f379a0e014
541decbea4a4
S3 binding_nonce: e509791018504c5bb87edaf0f44761cc840888507c4cd802379
71d78e65f70f2
S3 hiding_nonce_commitment: 0282308b1a22eb8efa13d4655f795f1cbf6525d88
63ac0d60c4e164b7436d41778
S3 binding_nonce_commitment: 036549bda4158ec5f76611275360a57e6ad5007d
6c072462feb42c8f2a25ec94ea
S3 binding_factor_input: 7a753fed12531fbcd151e1d84702927c39063e780e91
c01f02bd11b60d7632bf44df5a9e0d49f359549018a13a586b5ede02cadef80472f75
d195b82160f43ea0003
S3 binding_factor: 57a1061da0837cc0cd7e901a1d33f46efa18af9c3e6468cca8
8edd2d4a16e78d

// Round two parameters
participants: 1,3

// Signer round two outputs
S1 sig_share: 61e8b9c474df2e66ad19fd80a6e6cec1c6fe43c0a1cffd2d1c28299
e93e1bbdb
S3 sig_share: 9651d355ca1dea2557ba1f73e38a9f4ff1f1afc565323ef27f88a9d
14df8370e

sig: 02dfba781e17b830229ae4ed22ebe402873683d9dfd945d01762217fb3172c2a
71f83a8d1a3efd188c04d41cf48a716e11b8eff38607023c1f9bb0d36fe1d9f2e9
~~~
