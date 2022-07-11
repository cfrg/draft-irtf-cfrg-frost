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
FROST presented in this document requires two rounds to compute a signature, and implements
signing efficiency improvements described by {{Schnorr21}}. Single-round signing with FROST
is out of scope.

For select ciphersuites, the signatures produced by this draft are compatible with
{{!RFC8032}}. However, unlike {{!RFC8032}}, signatures produced by FROST are not
deterministic, since deriving nonces deterministically allows for a complete key-recovery
attack in multi-party discrete logarithm-based signatures, such as FROST.

Key generation for FROST signing is out of scope for this document. However, for completeness,
key generation with a trusted dealer is specified in {{dep-dealer}}.

## Change Log

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
{{ciphersuites}}. Using H, we introduce four separate domain-separated hashes,
H1, H2, H3, and H4, where H1, H2, and H4 map arbitrary byte strings to Scalar elements of
the prime-order group scalar field, and H3 is an alias for H with a domain separator.
The details of H1, H2, H3, and H4 vary based on ciphersuite. See {{ciphersuites}}
for more details about each.

# Helper functions {#helpers}

Beyond the core dependencies, the protocol in this document depends on the
following helper operations:

- Nonce generation, {{dep-nonces}}
- Schnorr signatures, {{dep-schnorr}};
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
    return H4(k_enc || secret_enc)
~~~

## Schnorr Signature Operations {#dep-schnorr}

In the single-party setting, a Schnorr signature is generated with the
following operation.

~~~
  schnorr_signature_generate(msg, sk):

  Inputs:
  - msg, message to be signed, a byte string
  - sk, private key, a Scalar

  Outputs: signature (R, z), a pair consisting of (Element, Scalar) values

  def schnorr_signature_generate(msg, sk):
    PK = G.ScalarBaseMult(sk)
    k = nonce_generate(sk)
    R = G.ScalarBaseMult(k)

    comm_enc = G.SerializeElement(R)
    pk_enc = G.SerializeElement(PK)
    challenge_input = comm_enc || pk_enc || msg
    c = H2(challenge_input)

    z = k + (c * sk)
    return (R, z)
~~~

The corresponding verification operation is as follows. By definition,
this function assumes that all group Elements passed as input, including
the signature R component and public key, belong to prime-order group G.
Some ciphersuites defined in {{ciphersuites}} operate in settings where
some inputs may not belong to this prime-order group, e.g., because they
operate over an elliptic curve with a cofactor larger than 1. In these
settings, input validation as specified in {{ciphersuites}} is required
before invoking this verification function.

~~~
  schnorr_signature_verify(msg, sig, PK):

  Inputs:
  - msg, signed message, a byte string
  - sig, a tuple (R, z) output from schnorr_signature_generate or FROST
  - PK, public key, an Element

  Outputs: 1 if signature is valid, and 0 otherwise

  def schnorr_signature_verify(msg, sig = (R, z), PK):
    comm_enc = G.SerializeElement(R)
    pk_enc = G.SerializeElement(PK)
    challenge_input = comm_enc || pk_enc || msg
    c = H2(challenge_input)

    l = G.ScalarBaseMult(z)
    r = R + (c * PK)
    return l == r
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

This section describes a helper function for extracting signer participant
identifiers from a commitment list. It also describes a helper function
for extracting a given participant's binding factor from a list.

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
  - binding_factors = [(i, binding_factor_i), ...],
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

  def compute_binding_factors(encoded_commitment_list, msg):
    msg_hash = H3(msg)
    binding_factor_list = []
    for (identifier, hiding_nonce_commitment, binding_nonce_commitment) in commitment_list:
      encoded_commitment = encode_uint16(identifier) ||
                           G.SerializeElement(hiding_nonce_commitment) ||
                           G.SerializeElement(binding_nonce_commitment)
      rho_input = encoded_commitment + msg_hash
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
  - identifier, Identifier i of the signer. Note identifier will never equal 0.
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

## FROST(Ed25519, SHA-512)

This ciphersuite uses edwards25519 for the Group and SHA-512 for the Hash function `H`
meant to produce signatures indistinguishable from Ed25519 as specified in {{!RFC8032}}.
The value of the contextString parameter is empty.

- Group: edwards25519 {{!RFC8032}}
  - Order: 2^252 + 27742317777372353535851937790883648493 (see {{?RFC7748}})
  - Identity: As defined in {{RFC7748}}.
  - RandomScalar: Implemented by repeatedly generating a random 32-byte string
    and invoking DeserializeScalar on the result until success.
  - SerializeElement: Implemented as specified in {{!RFC8032, Section 5.1.2}}.
  - DeserializeElement: Implemented as specified in {{!RFC8032, Section 5.1.3}}.
    Additionally, this function validates that the resulting element is not the group
    identity element and is in the prime-order subgroup. The latter check can
    be implemented by multiplying the resulting point by the cofactor (8) and
    checking that the result is not the identity element.
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
  - H3(m): Implemented as an alias for H, i.e., H(m).
  - H4(m): Implemented by computing H("nonce" || m), interpreting the 64-byte digest
    as a little-endian integer, and reducing the resulting integer modulo
    L = 2^252+27742317777372353535851937790883648493.

Normally H2 would also include a domain separator, but for backwards compatibility
with {{!RFC8032}}, it is omitted.

## FROST(ristretto255, SHA-512) {#recommended-suite}

This ciphersuite uses ristretto255 for the Group and SHA-512 for the Hash function `H`.
The value of the contextString parameter is "FROST-RISTRETTO255-SHA512-v5".

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
  - H3(m): Implemented by computing H(contextString \|\| "digest" \|\| m).
  - H4(m): Implemented by computing H(contextString || "nonce" || m) and mapping the
    output to a Scalar as described in {{!RISTRETTO, Section 4.4}}.

## FROST(Ed448, SHAKE256)

This ciphersuite uses edwards448 for the Group and SHAKE256 for the Hash function `H`
meant to produce signatures indistinguishable from Ed448 as specified in {{!RFC8032}}.
The value of the contextString parameter is empty.

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
  - H3(m): Implemented as an alias for H, i.e., H(m).
  - H4(m): Implemented by computing H("nonce" || m), interpreting the lower
    57 bytes as a little-endian integer, and reducing the resulting integer modulo
    L = 2^446 - 13818066809895115352007386748515426880336692474882178609894547503885.

Normally H2 would also include a domain separator, but for backwards compatibility
with {{!RFC8032}}, it is omitted.

## FROST(P-256, SHA-256)

This ciphersuite uses P-256 for the Group and SHA-256 for the Hash function `H`.
The value of the contextString parameter is "FROST-P256-SHA256-v5".

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
  - H3(m): Implemented by computing H(contextString \|\| "digest" \|\| m).
  - H4(m): Implemented using hash_to_field from {{!HASH-TO-CURVE, Section 5.3}}
    using L = 48, `expand_message_xmd` with SHA-256, DST = contextString || "nonce", and
    prime modulus equal to `Order()`.

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
S1 hiding_nonce: 424fb678c3cd26ae86813ed1e22f9074b2dec6b0fb39d748101a
9434d6c4c60a
S1 binding_nonce: 49c957d98fec37b81a491fcbc3b16af925d393d734acc765446
574bc7b453109
S1 hiding_nonce_commitment: 6ca4bc3e03fa91bd15ec29993bc0582779c1d0c60
2c3141b22ea76abf9384290
S1 binding_nonce_commitment: 03dc2bc626fc5fa41168dee456ec17bac8673691
e27547c534a559c3d4d7fc6b
S1 binding_factor_input: 00016ca4bc3e03fa91bd15ec29993bc0582779c1d0c6
02c3141b22ea76abf938429003dc2bc626fc5fa41168dee456ec17bac8673691e2754
7c534a559c3d4d7fc6bee26b0dd4af7e749aa1a8ee3c10ae9923f618980772e473f88
19a5d4940e0db27ac185f8a0e1d5f84f88bc887fd67b143732c304cc5fa9ad8e6f57f
50028a8ff
S1 binding_factor: 1af00d46730628637df21dd56023489d6691468b2515c28c22
052abc63e4d405
S3 hiding_nonce: bcca3084a26538abd5326825f7a1203907c09ae7d12160810c4c
8254aac02e03
S3 binding_nonce: 9063464ee91ee0981f0073783c7ca1590ed6b1cb7382bad842f
6a5a4dc7ba607
S3 hiding_nonce_commitment: 7786dc3db9823b1b2c81d71957d2464302ffc5b31
e586f9e754385e7d216a2d1
S3 binding_nonce_commitment: 21b0c507a779f3288c74506838e8f084cd378eab
4b66ce185fe842a2262ac899
S3 binding_factor_input: 00037786dc3db9823b1b2c81d71957d2464302ffc5b3
1e586f9e754385e7d216a2d121b0c507a779f3288c74506838e8f084cd378eab4b66c
e185fe842a2262ac899ee26b0dd4af7e749aa1a8ee3c10ae9923f618980772e473f88
19a5d4940e0db27ac185f8a0e1d5f84f88bc887fd67b143732c304cc5fa9ad8e6f57f
50028a8ff
S3 binding_factor: 7702669b34a9534bce0e73ed97c3d002433d969f4ee70c4a30
c6f56e661efb0e

// Round two parameters
participants: 1,3

// Signer round two outputs
S1 sig_share: 95bac1faca14c3f85d9f3b5d515009a2db7715cdafaa414bb5d271a
2f1300c0c
S3 sig_share: 636280b4886b8120e2aeffd6637f82e64a4616c1b65682bb4a68863
5c4bd3107

sig: ad05ed58d78f26dba585d4e452b099126f733bc35c698210ce8590691582e387
0b494c52391d32c169b14391d6d5ac7326be2b8e6601c406003bf8d7b5ee3d03
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
S1 hiding_nonce: d1c4212b1b0987135b686fc1e0c26d464609e3b2cb0363f4ce81
676d9798c10161775894edae39f91731083a8751b754ce7faa9b51bd3c1800
S1 binding_nonce: c1f429e6b853dfefac16acebba0691916b5e41ea62122a7d565
b16c98069202f6e18cba21790f26a351253ce03ff41556435ac7a1ce6960d00
S1 hiding_nonce_commitment: cc1cb80545250515c06b5b5c2ae124973a232d7bf
74fd2b3d4f9ba0505b67ee3eee3f10b1c8a739b5eedd49158e0b4a1789ec3b4aef2f6
4280
S1 binding_nonce_commitment: 5d0766016f294cc27af4a94a1f6f0c1e4074377d
7850133fa6e56ee6073e47fe0e3e0b9af5a8a4c24d179f2711702d9232557e72e7f04
9ec00
S1 binding_factor_input: 0001cc1cb80545250515c06b5b5c2ae124973a232d7b
f74fd2b3d4f9ba0505b67ee3eee3f10b1c8a739b5eedd49158e0b4a1789ec3b4aef2f
642805d0766016f294cc27af4a94a1f6f0c1e4074377d7850133fa6e56ee6073e47fe
0e3e0b9af5a8a4c24d179f2711702d9232557e72e7f049ec00b54ff7255705a71ee29
25e4a3e30e41aed489a579d5595e0df13e32e1e4dd202a7c7f68b31d6418d9845eb4d
757adda6ab189e1bb340db818e5b3bc725d992faf63e9b0500db10517fe09d3f566fb
a3a80e46a403e0c7d41548fbf75cf2662b00225b502961f98d8c9ff937de0b24c2318
45
S1 binding_factor: 2648c00456a49c45068225a53daf4141c49d94f24c91baa0c4
709b929652b678533533da023bc86546d2bf27103401069e82e7d76e45d80700
S3 hiding_nonce: 27c798a453fdc42aee7302b02140622fe17a99aa57f61dc5f9ce
0e55cf64034cfe41954d8e4d4bc46bad25b67058e9d8de87cee9dcea340f00
S3 binding_nonce: 2fdf07df954ce0378e47551841db9826e8ceec79c083f4e1e70
5d1f14824784dc82dade69b01065e9483d8c6cc577afa15c60484fe670e0500
S3 hiding_nonce_commitment: 7f4e108990f82c411317c5e1f945b46e3c115a52c
60e57a360fbc69c3101ca4b3151b855f7c28574ce2e6a4150fcb351d50bb81fec3d03
f500
S3 binding_nonce_commitment: ac79cf898abd0896a1468944f40b38cfb82cb191
c737681d0b8b2d1a6bebb559ae0221cda231238caf603e2ee85658bc28782083ecd3a
ab900
S3 binding_factor_input: 00037f4e108990f82c411317c5e1f945b46e3c115a52
c60e57a360fbc69c3101ca4b3151b855f7c28574ce2e6a4150fcb351d50bb81fec3d0
3f500ac79cf898abd0896a1468944f40b38cfb82cb191c737681d0b8b2d1a6bebb559
ae0221cda231238caf603e2ee85658bc28782083ecd3aab900b54ff7255705a71ee29
25e4a3e30e41aed489a579d5595e0df13e32e1e4dd202a7c7f68b31d6418d9845eb4d
757adda6ab189e1bb340db818e5b3bc725d992faf63e9b0500db10517fe09d3f566fb
a3a80e46a403e0c7d41548fbf75cf2662b00225b502961f98d8c9ff937de0b24c2318
45
S3 binding_factor: b165cef8a42b605d192930206ffcdf48cf242e968340c9e13f
58962be27bccb2af4d674e67c3e97ff719ba87216565544edb1f862c18433e00

// Round two parameters
participants: 1,3

// Signer round two outputs
S1 sig_share: c0c5055e6429cf24c60fd19cb7e887caed243db821f81fc899a30f2
dae833bf6c373acb0a0dbd9d7d3bd3de36e1b33b21ea9c19dce74d23b00
S3 sig_share: 495e6971b5ab6bf800860296eeb8e0caa4a8b2137f390b53366bb97
432dbf0fc07b315fa9df67eda1417720fc98f9325340d7fb8fe708a2f00

sig: 6d244abe9f23024c58b1962baec45a0cce035d7a73034ca39642ed58df8dd444
f8f2a3e08b187645fecdd93fbd151af076e608b976206bbe8016df16248712c2f9710
60ea533dffb730297191d5756dc56e6eafe24e15e2cf3cb26c2aa3ed258b2e8d4aff2
37abc6d752b64056cde55c2b00
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
S1 hiding_nonce: 82fd8f26f0b5f86d93d3da8162c23641aa1b16ab803be1a4d850
0f143b592605
S1 binding_nonce: c9ee2f764434e263808722a3cb9886b7ce25ade80ce00bac4ac
4d9548ac2450a
S1 hiding_nonce_commitment: c4f0ea06e07ee8e41bd3de3a63dc77f40d65a7ede
329263db410eb0e455c9a7a
S1 binding_nonce_commitment: c2ab142e4c2572aea1dcd0044e864544c49874b2
e39ed5f969b6133372a23643
S1 binding_factor_input: 0001c4f0ea06e07ee8e41bd3de3a63dc77f40d65a7ed
e329263db410eb0e455c9a7ac2ab142e4c2572aea1dcd0044e864544c49874b2e39ed
5f969b6133372a23643678630bf982c566949d7f22d2aefb94f252c664216d332f34e
2c8fdcd7045f207f854504d0daa534a5b31dbdf4183be30eb4fdba4f962d8a6b69cf2
0c2734043
S1 binding_factor: 1bed7e23dbe3066085a132da86ccf1e58291cec6571249cd4f
16a053c8409b04
S3 hiding_nonce: d2478a9a47594005cb6de147f4c98b92b5e27e157fddb37ef122
a75dfd7b8e06
S3 binding_nonce: 5f2193dc5f3e5537fba742786fec22e18e40b059e50d6ef2e31
60a3faf11dd0e
S3 hiding_nonce_commitment: 9a543be2b522d20a9d7e920388bb32f954bcfc695
d145736de09f09646c6ae4c
S3 binding_nonce_commitment: debe73bc386b4dba161d72fa46ecc86765d6ff36
27cfe07d56891d21399f1e4c
S3 binding_factor_input: 00039a543be2b522d20a9d7e920388bb32f954bcfc69
5d145736de09f09646c6ae4cdebe73bc386b4dba161d72fa46ecc86765d6ff3627cfe
07d56891d21399f1e4c678630bf982c566949d7f22d2aefb94f252c664216d332f34e
2c8fdcd7045f207f854504d0daa534a5b31dbdf4183be30eb4fdba4f962d8a6b69cf2
0c2734043
S3 binding_factor: f611130beed6aa69de48fc1c05e7a005c7d5232b2852fe721a
1d711c35a28600

// Round two parameters
participants: 1,3

// Signer round two outputs
S1 sig_share: 2aeac152cff93a82233c1ac6bece654af750f75c47cd5c87fcf6109
a562c8903
S3 sig_share: a9487edfb9349f792693278fa9f8abd57c2caaac4f901fb03da8534
c56574303

sig: a6fa7f7553307cfa36e55a705a2e59f808a1bcda888efcf4f26ba0c4080cc400
d3324032892edafb49cf415568c71120747da109975d7c373a9f64e6ac83cc06
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
S1 hiding_nonce: e1bec1511c502e6b6866ef35469dac6df913efa8042a70b39aa6
494307d6ee41
S1 binding_nonce: 55682738caade073b207abdec93014bc111bc5d6a8977f3a24d
f58bebf650894
S1 hiding_nonce_commitment: 0257ea635b11b63eb125ed1c983082a406e0185e5
df6bd4c2a708f7d4b1ffe72d2
S1 binding_nonce_commitment: 03aec5dfcd35c5ad7a7242552efe9c45878a0b2f
3f576b8f60fa172d380881f040
S1 binding_factor_input: 00010257ea635b11b63eb125ed1c983082a406e0185e
5df6bd4c2a708f7d4b1ffe72d203aec5dfcd35c5ad7a7242552efe9c45878a0b2f3f5
76b8f60fa172d380881f0407a753fed12531fbcd151e1d84702927c39063e780e91c0
1f02bd11b60d7632bf
S1 binding_factor: 846723bf0898010ebb3d0a0c193c682a22946bb99c9551f5e3
a0c29008aa8891
S3 hiding_nonce: a284c689cd1d8ec33dcfe840d18ba0ddcbb69571744116912d7a
5c20631ea003
S3 binding_nonce: 9f3ca4297e01ce82a5c7301a8fc39e6ec0588087483c912e269
92f0d00009f0b
S3 hiding_nonce_commitment: 02fc8fe2f5d1bfa6b027ff1184c57cc7b880e050f
bf370a4e23d17eb3b249f45d9
S3 binding_nonce_commitment: 02288d41169a97462b323dd61658eb134f8dd802
af7d1932f602f2532afd9d1903
S3 binding_factor_input: 000302fc8fe2f5d1bfa6b027ff1184c57cc7b880e050
fbf370a4e23d17eb3b249f45d902288d41169a97462b323dd61658eb134f8dd802af7
d1932f602f2532afd9d19037a753fed12531fbcd151e1d84702927c39063e780e91c0
1f02bd11b60d7632bf
S3 binding_factor: 739b96f69c0ec5fbe05c2f5191ec349f835d9a38f8cf1a5632
87b3547540c4b0

// Round two parameters
participants: 1,3

// Signer round two outputs
S1 sig_share: 38f57b8c861a9eb03eeeb381bae58f0f7fce6f0d0da431a0ae58a00
a760aadf4
S3 sig_share: e4f1da04a879bd5b23c51662c22cbd71a80129db5e387895c769727
a15176556

sig: 02b72e3a186d719efb18f4341d7b5d983f782d31c57f884a5fe79040d30ddd39
381de755922e945c0a62b3c9e47d124c816ae89e3ac4c50bb1820847c18ebeedf9
~~~
