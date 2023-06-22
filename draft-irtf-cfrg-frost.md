---
title: "Two-Round Threshold Schnorr Signatures with FROST"
abbrev: "FROST"
docname: draft-irtf-cfrg-frost-latest
category: info
submissiontype: IRTF

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
  StrongerSec22:
    target: https://crypto.iacr.org/2022/papers/538806_1_En_18_Chapter_OnlinePDF.pdf
    title: "Better than Advertised Security for Non-interactive Threshold Signatures"
    author:
      - name: Mihir Bellare
      - name: Elizabeth Crites
      - name: Chelsea Komlo
      - name: Mary Maller
      - name: Stefano Tessaro
      - name: Chenzhi Zhu
    date: 2022-06-01
  Pornin22:
    target: https://eprint.iacr.org/2022/1164.pdf
    title: "Point-Halving and Subgroup Membership in Twisted Edwards Curves"
    author:
      - name: Thomas Pornin
    date: 2022-09-06
  ROAST:
    target: https://eprint.iacr.org/2022/550
    title: "ROAST: Robust Asynchronous Schnorr Threshold Signatures"
    author:
      - name: Tim Ruffing
      - name: Viktoria Ronge
      - name: Elliott Jin
      - name: Jonas Schneider-Bensch
      - name: Dominique Schröder
    date: 2022-09-18

--- abstract

This document specifies the Flexible Round-Optimized Schnorr Threshold (FROST) signing protocol.
FROST signatures can be issued after a threshold number of entities cooperate to
compute a signature, allowing for improved distribution of trust and
redundancy with respect to a secret key. FROST depends only on a prime-order group and cryptographic
hash function. This document specifies a number of ciphersuites to instantiate FROST using different
prime-order groups and hash functions. One such ciphersuite can be used to produce signatures
that can be verified with an Edwards-Curve Digital Signature Algorithm (EdDSA, as defined in RFC8032)
compliant verifier. However, unlike EdDSA, the signatures produced by FROST are not deterministic.
This document is a product of the Crypto Forum Research Group (CFRG) in the IRTF.

--- middle

# Introduction

RFC EDITOR: PLEASE REMOVE THE FOLLOWING PARAGRAPH The source for this draft is
maintained in GitHub. Suggested changes should be submitted as pull requests
at https://github.com/cfrg/draft-irtf-cfrg-frost. Instructions are on that page as
well.

Unlike signatures in a single-party setting, threshold signatures
require cooperation among a threshold number of signing participants each holding a share
of a common private key. The security of threshold schemes in general assumes
that an adversary can corrupt strictly fewer than a threshold number of signer participants.

This document specifies the Flexible Round-Optimized Schnorr Threshold (FROST) signing protocol
based on the original work in {{FROST20}}. FROST reduces network overhead during
threshold signing operations while employing a novel technique to protect against forgery
attacks applicable to prior Schnorr-based threshold signature constructions. FROST requires
two rounds to compute a signature. Single-round signing variants based on {{FROST20}} are out of scope.

FROST depends only on a prime-order group and cryptographic hash function. This document specifies
a number of ciphersuites to instantiate FROST using different prime-order groups and hash functions.
Two ciphersuites can be used to produce signatures that are compatible with Edwards-Curve Digital
Signature Algorithm (EdDSA) variants Ed25519 and Ed448 as specified in {{!RFC8032}}, i.e., the
signatures can be verified with an {{!RFC8032}} compliant verifier. However, unlike EdDSA, the
signatures produced by FROST are not deterministic, since deriving nonces deterministically allows
for a complete key-recovery attack in multi-party discrete logarithm-based signatures.

Key generation for FROST signing is out of scope for this document. However, for completeness,
key generation with a trusted dealer is specified in {{dep-dealer}}.

This document represents the consensus of the Crypto Forum Research
Group (CFRG). It is not an IETF product and is not a standard.

## Change Log

draft-12

- Address RGLC feedback (#399, #396, #395, #394, #393, #384, #382, #397, #378, #376, #375, #374, #373, #371, #370, #369, #368, #367, #366, #364, #363, #362, #361, #359, #358, #357, #356, #354, #353, #352, #350, #349, #348, #347, #314)
- Fix bug in signature share serialization (#397)
- Fix various editorial issues (#385)

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

* byte: A sequence of eight bits.
* `random_bytes(n)`: Outputs `n` bytes, sampled uniformly at random
using a cryptographically secure pseudorandom number generator (CSPRNG).
* `count(i, L)`: Outputs the number of times the element `i` is represented in the list `L`.
* `len(l)`: Outputs the length of list `l`, e.g., `len([1,2,3]) = 3`.
* `reverse(l)`: Outputs the list `l` in reverse order, e.g., `reverse([1,2,3]) = [3,2,1]`.
* `range(a, b)`: Outputs a list of integers from `a` to `b-1` in ascending order, e.g., `range(1, 4) = [1,2,3]`.
* `pow(a, b)`: Outputs the result, a Scalar, of `a` to the power of `b`, e.g., `pow(2, 3) = 8` modulo the relevant group order `p`.
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
scalar addition, depending on the type of the operands.) For any element `A`, `ScalarMult(A, p) = I`.
We denote `B` as a fixed generator of the group. Scalar base multiplication is equivalent to the repeated application
of the group operation on `B` with itself `r-1` times, this is denoted as `ScalarBaseMult(r)`. The set of
scalars corresponds to `GF(p)`, which we refer to as the scalar field. It is assumed that
group element addition, negation, and equality comparison can be efficiently computed for
arbitrary group elements.

This document uses types `Element` and `Scalar` to denote elements of the group `G` and
its set of scalars, respectively. We denote Scalar(x) as the conversion of integer input `x`
to the corresponding Scalar value with the same numeric value. For example, Scalar(1) yields
a Scalar representing the value 1. Moreover, we use the type `NonZeroScalar` to denote a `Scalar`
value that is not equal to zero, i.e., Scalar(0). We denote equality comparison of these types
as `==` and assignment of values by `=`. When comparing Scalar values, e.g., for the purposes
of sorting lists of Scalar values, the least nonnegative representation mod `p` is used.

We now detail a number of member functions that can be invoked on `G`.

- Order(): Outputs the order of `G` (i.e., `p`).
- Identity(): Outputs the identity `Element` of the group (i.e., `I`).
- RandomScalar(): Outputs a random `Scalar` element in GF(p), i.e., a random scalar in \[0, p - 1\].
- ScalarMult(A, k): Outputs the scalar multiplication between Element `A` and Scalar `k`.
- ScalarBaseMult(k): Outputs the scalar multiplication between Scalar `k` and the group generator `B`.
- SerializeElement(A): Maps an `Element` `A` to a canonical byte array `buf` of fixed length `Ne`. This
  function raises an error if `A` is the identity element of the group.
- DeserializeElement(buf): Attempts to map a byte array `buf` to an `Element` `A`,
  and fails if the input is not the valid canonical byte representation of an element of
  the group. This function raises an error if deserialization fails
  or if `A` is the identity element of the group; see {{ciphersuites}} for group-specific
  input validation steps.
- SerializeScalar(s): Maps a Scalar `s` to a canonical byte array `buf` of fixed length `Ns`.
- DeserializeScalar(buf): Attempts to map a byte array `buf` to a `Scalar` `s`.
  This function raises an error if deserialization fails; see
  {{ciphersuites}} for group-specific input validation steps.

## Cryptographic Hash Function {#dep-hash}

FROST requires the use of a cryptographically secure hash function, generically
written as H, which is modeled as a random oracle in security proofs for the protocol
(see {{FROST20}} and {{StrongerSec22}}). For concrete recommendations on hash functions
which SHOULD be used in practice, see {{ciphersuites}}. Using H, we introduce distinct
domain-separated hashes, H1, H2, H3, H4, and H5:

- H1, H2, and H3 map arbitrary byte strings to Scalar elements associated with the prime-order group.
- H4 and H5 are aliases for H with distinct domain separators.

The details of H1, H2, H3, H4, and H5 vary based on ciphersuite. See {{ciphersuites}}
for more details about each.

# Helper Functions {#helpers}

Beyond the core dependencies, the protocol in this document depends on the
following helper operations:

- Nonce generation, {{dep-nonces}};
- Polynomials, {{dep-polynomial}};
- Encoding operations, {{dep-encoding}};
- Signature binding computation {{dep-binding-factor}};
- Group commitment computation {{dep-group-commit}}; and
- Signature challenge computation {{dep-sig-challenge}}.

The following sections describe these operations in more detail.

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
Inputs:
- secret, a Scalar.

Outputs:
- nonce, a Scalar.

def nonce_generate(secret):
  random_bytes = random_bytes(32)
  secret_enc = G.SerializeScalar(secret)
  return H3(random_bytes || secret_enc)
~~~

## Polynomials {#dep-polynomial}

This section defines polynomials over Scalars that are used in the main protocol.
A polynomial of maximum degree t is represented as a list of t+1 coefficients,
where the constant term of the polynomial is in the first position and the
highest-degree coefficient is in the last position. For example, the polynomial
`x^2 + 2x + 3` has degree 2 and is represented as a list of 3 coefficients `[3, 2, 1]`.
A point on the polynomial `f` is a tuple (x, y), where `y = f(x)`.

The function `derive_interpolating_value` derives a value used for polynomial
interpolation. It is provided a list of x-coordinates as input, each of which
cannot equal 0.

~~~
Inputs:
- L, the list of x-coordinates, each a NonZeroScalar.
- x_i, an x-coordinate contained in L, a NonZeroScalar.

Outputs:
- value, a Scalar.

Errors:
- "invalid parameters", if 1) x_i is not in L, or if 2) any
  x-coordinate is represented more than once in L.

def derive_interpolating_value(L, x_i):
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

  value = numerator / denominator
  return value
~~~

## List Operations {#dep-encoding}

This section describes helper functions that work on lists of values produced
during the FROST protocol. The following function encodes a list of participant
commitments into a byte string for use in the FROST protocol.

~~~
Inputs:
- commitment_list = [(i, hiding_nonce_commitment_i,
  binding_nonce_commitment_i), ...], a list of commitments issued by
  each participant, where each element in the list indicates a
  NonZeroScalar identifier i and two commitment Element values
  (hiding_nonce_commitment_i, binding_nonce_commitment_i). This list
  MUST be sorted in ascending order by identifier.

Outputs:
- encoded_group_commitment, the serialized representation of
  commitment_list, a byte string.

def encode_group_commitment_list(commitment_list):
  encoded_group_commitment = nil
  for (identifier, hiding_nonce_commitment,
       binding_nonce_commitment) in commitment_list:
    encoded_commitment = (
        G.SerializeScalar(identifier) ||
        G.SerializeElement(hiding_nonce_commitment) ||
        G.SerializeElement(binding_nonce_commitment))
    encoded_group_commitment = (
        encoded_group_commitment ||
        encoded_commitment)
  return encoded_group_commitment
~~~

The following function is used to extract identifiers from a commitment list.

~~~
Inputs:
- commitment_list = [(i, hiding_nonce_commitment_i,
  binding_nonce_commitment_i), ...], a list of commitments issued by
  each participant, where each element in the list indicates a
  NonZeroScalar identifier i and two commitment Element values
  (hiding_nonce_commitment_i, binding_nonce_commitment_i). This list
  MUST be sorted in ascending order by identifier.

Outputs:
- identifiers, a list of NonZeroScalar values.

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
  a list of binding factors for each participant, where each element
  in the list indicates a NonZeroScalar identifier i and Scalar
  binding factor.
- identifier, participant identifier, a NonZeroScalar.

Outputs:
- binding_factor, a Scalar.

Errors:
- "invalid participant", when the designated participant is
  not known.

def binding_factor_for_participant(binding_factor_list, identifier):
  for (i, binding_factor) in binding_factor_list:
    if identifier == i:
      return binding_factor
  raise "invalid participant"
~~~

## Binding Factors Computation {#dep-binding-factor}

This section describes the subroutine for computing binding factors based
on the participant commitment list, message to be signed, and group public key.

~~~
Inputs:
- group_public_key, the public key corresponding to the group signing
  key, an Element.
- commitment_list = [(i, hiding_nonce_commitment_i,
  binding_nonce_commitment_i), ...], a list of commitments issued by
  each participant, where each element in the list indicates a
  NonZeroScalar identifier i and two commitment Element values
  (hiding_nonce_commitment_i, binding_nonce_commitment_i). This list
  MUST be sorted in ascending order by identifier.
- msg, the message to be signed.

Outputs:
- binding_factor_list, a list of (NonZeroScalar, Scalar) tuples
  representing the binding factors.

def compute_binding_factors(group_public_key, commitment_list, msg):
  group_public_key_enc = G.SerializeElement(group_public_key)
  // Hashed to a fixed-length.
  msg_hash = H4(msg)
  // Hashed to a fixed-length.
  encoded_commitment_hash =
      H5(encode_group_commitment_list(commitment_list))
  // The encoding of the group public key is a fixed length within a ciphersuite.
  rho_input_prefix = group_public_key_enc || msg_hash || encoded_commitment_hash

  binding_factor_list = []
  for (identifier, hiding_nonce_commitment,
       binding_nonce_commitment) in commitment_list:
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
- commitment_list = [(i, hiding_nonce_commitment_i,
  binding_nonce_commitment_i), ...], a list of commitments issued by
  each participant, where each element in the list indicates a
  NonZeroScalar identifier i and two commitment Element values
  (hiding_nonce_commitment_i, binding_nonce_commitment_i). This list
  MUST be sorted in ascending order by identifier.
- binding_factor_list = [(i, binding_factor), ...],
  a list of (NonZeroScalar, Scalar) tuples representing the binding
  factor Scalar for the given identifier.

Outputs:
- group_commitment, an Element.

def compute_group_commitment(commitment_list, binding_factor_list):
  group_commitment = G.Identity()
  for (identifier, hiding_nonce_commitment,
       binding_nonce_commitment) in commitment_list:
    binding_factor = binding_factor_for_participant(
        binding_factor_list, identifier)
    binding_nonce = G.ScalarMult(
        binding_nonce_commitment,
        binding_factor)
    group_commitment = (
        group_commitment +
        hiding_nonce_commitment +
        binding_nonce)
  return group_commitment
~~~

## Signature Challenge Computation {#dep-sig-challenge}

This section describes the subroutine for creating the per-message challenge.

~~~
Inputs:
- group_commitment, the group commitment, an Element.
- group_public_key, the public key corresponding to the group signing
  key, an Element.
- msg, the message to be signed, a byte string.

Outputs:
- challenge, a Scalar.

def compute_challenge(group_commitment, group_public_key, msg):
  group_comm_enc = G.SerializeElement(group_commitment)
  group_public_key_enc = G.SerializeElement(group_public_key)
  challenge_input = group_comm_enc || group_public_key_enc || msg
  challenge = H2(challenge_input)
  return challenge
~~~

# Two-Round FROST Signing Protocol {#frost-spec}

This section describes the two-round FROST signing protocol for producing Schnorr signatures.
The protocol is configured to run with a selection of `NUM_PARTICIPANTS` signer participants and a Coordinator.
`NUM_PARTICIPANTS` is a positive integer at least `MIN_PARTICIPANTS` but no larger than
`MAX_PARTICIPANTS`, where `MIN_PARTICIPANTS <= MAX_PARTICIPANTS`, `MIN_PARTICIPANTS` is a positive
non-zero integer and `MAX_PARTICIPANTS` is a positive integer less than the group order.
A signer participant, or simply participant, is an entity that is trusted to hold and
use a signing key share. The Coordinator is an entity with the following responsibilities:

1. Determining which participants will participate (at least MIN_PARTICIPANTS in number);
2. Coordinating rounds (receiving and forwarding inputs among participants); and
3. Aggregating signature shares output by each participant, and publishing the resulting signature.

FROST assumes that the Coordinator and the set of signer participants are chosen
externally to the protocol. Note that it is possible to deploy the protocol without
a distinguished Coordinator; see {{no-coordinator}} for more information.

FROST produces signatures that can be verified as if they were produced from a single signer
using a signing key `s` with corresponding public key `PK`, where `s` is a Scalar
value and `PK = G.ScalarBaseMult(s)`. As a threshold signing protocol, the group signing
key `s` is Shamir secret-shared amongst each of the `MAX_PARTICIPANTS` participants
and used to produce signatures; see {{dep-shamir}} for more information about Shamir secret sharing.
In particular, FROST assumes each participant is configured with the following information:

- An identifier, which is a NonZeroScalar value denoted `i` in the range `[1, MAX_PARTICIPANTS]`
  and MUST be distinct from the identifier of every other participant.
- A signing key `sk_i`, which is a Scalar value representing the i-th Shamir secret share
  of the group signing key `s`. In particular, `sk_i` is the value `f(i)` on a secret
  polynomial `f` of degree `(MIN_PARTICIPANTS - 1)`, where `s` is `f(0)`. The public key
  corresponding to this signing key share is `PK_i = G.ScalarBaseMult(sk_i)`.

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

FROST requires two rounds to complete. In the first round, participants generate
and publish one-time-use commitments to be used in the second round. In the second
round, each participant produces a share of the signature over the Coordinator-chosen
message and the other participant commitments. After the second round completes, the
Coordinator aggregates the signature shares to produce a final signature. The Coordinator
SHOULD abort if the signature is invalid; see {{abort}} for more information about dealing
with invalid signatures and misbehaving participants. This complete interaction,
without abort, is shown in {{fig-frost}}.

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
{: #fig-frost title="FROST protocol overview" }

Details for round one are described in {{frost-round-one}}, and details for round two
are described in {{frost-round-two}}. Note that each participant persists some state between
the two rounds, and this state is deleted as described in {{frost-round-two}}. The final
Aggregation step is described in {{frost-aggregation}}.

FROST assumes that all inputs to each round, especially those of which are received
over the network, are validated before use. In particular, this means that any value
of type Element or Scalar is deserialized using DeserializeElement and DeserializeScalar,
respectively, as these functions perform the necessary input validation steps, and that all
messages sent over the wire are encoded appropriately, e.g., that Scalars and Elements are
encoded using their respective functions.

FROST assumes reliable message delivery between the Coordinator and participants in
order for the protocol to complete. An attacker masquerading as another participant
will result only in an invalid signature; see {{sec-considerations}}. However, in order
to identify misbehaving participants,
we assume that the network channel is additionally authenticated; confidentiality is
not required.

## Round One - Commitment {#frost-round-one}

Round one involves each participant generating nonces and their corresponding public commitments.
A nonce is a pair of Scalar values, and a commitment is a pair of Element values. Each participant's
behavior in this round is described by the `commit` function below. Note that this function
invokes `nonce_generate` twice, once for each type of nonce produced. The output of this function is
a pair of secret nonces `(hiding_nonce, binding_nonce)` and their corresponding public commitments
`(hiding_nonce_commitment, binding_nonce_commitment)`.

~~~
Inputs:
- sk_i, the secret key share, a Scalar.

Outputs:
- (nonce, comm), a tuple of nonce and nonce commitment pairs,
  where each value in the nonce pair is a Scalar and each value in
  the nonce commitment pair is an Element.

def commit(sk_i):
  hiding_nonce = nonce_generate(sk_i)
  binding_nonce = nonce_generate(sk_i)
  hiding_nonce_commitment = G.ScalarBaseMult(hiding_nonce)
  binding_nonce_commitment = G.ScalarBaseMult(binding_nonce)
  nonces = (hiding_nonce, binding_nonce)
  comms = (hiding_nonce_commitment, binding_nonce_commitment)
  return (nonces, comms)
~~~

The outputs `nonce` and `comm` from participant `P_i` should both be stored locally and
kept for use in the second round. The `nonce` value is secret and MUST NOT be shared, whereas
the public output `comm` is sent to the Coordinator. The nonce values produced by this
function MUST NOT be used in more than one invocation of `sign`, and the nonces MUST be generated
from a source of secure randomness.

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
its identifier and commitments (from the first round) appear in commitment_list.
Applications which require that participants not process arbitrary
input messages are also required to perform relevant application-layer input
validation checks; see {{message-validation}} for more details.

Upon receipt and successful input validation, each Signer then runs the following
procedure to produce its own signature share.

~~~
Inputs:
- identifier, identifier i of the participant, a NonZeroScalar.
- sk_i, Signer secret key share, a Scalar.
- group_public_key, public key corresponding to the group signing
  key, an Element.
- nonce_i, pair of Scalar values (hiding_nonce, binding_nonce)
  generated in round one.
- msg, the message to be signed, a byte string.
- commitment_list = [(i, hiding_nonce_commitment_i,
  binding_nonce_commitment_i), ...], a list of commitments issued by
  each participant, where each element in the list indicates a
  NonZeroScalar identifier i and two commitment Element values
  (hiding_nonce_commitment_i, binding_nonce_commitment_i). This list
  MUST be sorted in ascending order by identifier.


Outputs:
- sig_share, a signature share, a Scalar.

def sign(identifier, sk_i, group_public_key,
         nonce_i, msg, commitment_list):
  # Compute the binding factor(s)
  binding_factor_list = compute_binding_factors(group_public_key, commitment_list, msg)
  binding_factor = binding_factor_for_participant(
      binding_factor_list, identifier)

  # Compute the group commitment
  group_commitment = compute_group_commitment(
      commitment_list, binding_factor_list)

  # Compute the interpolating value
  participant_list = participants_from_commitment_list(
      commitment_list)
  lambda_i = derive_interpolating_value(participant_list, identifier)

  # Compute the per-message challenge
  challenge = compute_challenge(
      group_commitment, group_public_key, msg)

  # Compute the signature share
  (hiding_nonce, binding_nonce) = nonce_i
  sig_share = hiding_nonce + (binding_nonce * binding_factor) +
      (lambda_i * sk_i * challenge)

  return sig_share
~~~

The output of this procedure is a signature share. Each participant then sends
these shares back to the Coordinator. Each participant MUST delete the nonce and
corresponding commitment after completing `sign`, and MUST NOT use the nonce
as input more than once to `sign`.

Note that the `lambda_i` value derived during this procedure does not change
across FROST signing operations for the same signing group. As such, participants
can compute it once and store it for reuse across signing sessions.

## Signature Share Aggregation {#frost-aggregation}

After participants perform round two and send their signature shares to the Coordinator,
the Coordinator aggregates each share to produce a final signature. Before aggregating,
the Coordinator MUST validate each signature share using DeserializeScalar. If validation
fails, the Coordinator MUST abort the protocol as the resulting signature will be invalid.
If all signature shares are valid, the Coordinator aggregates them to produce the final
signature using the following procedure.

~~~
Inputs:
- commitment_list = [(i, hiding_nonce_commitment_i,
  binding_nonce_commitment_i), ...], a list of commitments issued by
  each participant, where each element in the list indicates a
  NonZeroScalar identifier i and two commitment Element values
  (hiding_nonce_commitment_i, binding_nonce_commitment_i). This list
  MUST be sorted in ascending order by identifier.
- msg, the message to be signed, a byte string.
- group_public_key, public key corresponding to the group signing
  key, an Element.
- sig_shares, a set of signature shares z_i, Scalar values, for each
  participant, of length NUM_PARTICIPANTS, where
  MIN_PARTICIPANTS <= NUM_PARTICIPANTS <= MAX_PARTICIPANTS.

Outputs:
- (R, z), a Schnorr signature consisting of an Element R and
  Scalar z.

def aggregate(commitment_list, msg, group_public_key, sig_shares):
  # Compute the binding factors
  binding_factor_list = compute_binding_factors(group_public_key, commitment_list, msg)

  # Compute the group commitment
  group_commitment = compute_group_commitment(
      commitment_list, binding_factor_list)

  # Compute aggregated signature
  z = Scalar(0)
  for z_i in sig_shares:
    z = z + z_i
  return (group_commitment, z)
~~~

The output from the aggregation step is the output signature (R, z). The canonical encoding
of this signature is specified in {{ciphersuites}}.

The Coordinator SHOULD verify this signature using the group public key before publishing or
releasing the signature. Signature verification is as specified for the corresponding
ciphersuite; see {{ciphersuites}} for details. The aggregate signature will verify successfully
if all signature shares are valid. Moreover, subsets of valid signature shares will themselves not yield
a valid aggregate signature.

If the aggregate signature verification fails, the Coordinator can verify each signature
share individually to identify and act on misbehaving participants. The mechanism for acting on
a misbehaving participant is out of scope for this specification; see {{abort}} for more information
about dealing with invalid signatures and misbehaving participants.

The function for verifying a signature share, denoted `verify_signature_share`, is described below.
Recall that the Coordinator is configured with "group info" which contains
the group public key `PK` and public keys `PK_i` for each participant, so the `group_public_key` and
`PK_i` function arguments should come from that previously stored group info.

~~~
Inputs:
- identifier, identifier i of the participant, a NonZeroScalar.
- PK_i, the public key for the i-th participant, where
  PK_i = G.ScalarBaseMult(sk_i), an Element.
- comm_i, pair of Element values in G
  (hiding_nonce_commitment, binding_nonce_commitment) generated in
  round one from the i-th participant.
- sig_share_i, a Scalar value indicating the signature share as
  produced in round two from the i-th participant.
- commitment_list = [(i, hiding_nonce_commitment_i,
  binding_nonce_commitment_i), ...], a list of commitments issued by
  each participant, where each element in the list indicates a
  NonZeroScalar identifier i and two commitment Element values
  (hiding_nonce_commitment_i, binding_nonce_commitment_i). This list
  MUST be sorted in ascending order by identifier.
- group_public_key, public key corresponding to the group signing
  key, an Element.
- msg, the message to be signed, a byte string.

Outputs:
- True if the signature share is valid, and False otherwise.

def verify_signature_share(
        identifier, PK_i, comm_i, sig_share_i, commitment_list,
        group_public_key, msg):
  # Compute the binding factors
  binding_factor_list = compute_binding_factors(group_public_key, commitment_list, msg)
  binding_factor = binding_factor_for_participant(
      binding_factor_list, identifier)

  # Compute the group commitment
  group_commitment = compute_group_commitment(
      commitment_list, binding_factor_list)

  # Compute the commitment share
  (hiding_nonce_commitment, binding_nonce_commitment) = comm_i
  comm_share = hiding_nonce_commitment + G.ScalarMult(
      binding_nonce_commitment, binding_factor)

  # Compute the challenge
  challenge = compute_challenge(
      group_commitment, group_public_key, msg)

  # Compute the interpolating value
  participant_list = participants_from_commitment_list(
      commitment_list)
  lambda_i = derive_interpolating_value(x_list, identifier)

  # Compute relation values
  l = G.ScalarBaseMult(sig_share_i)
  r = comm_share + G.ScalarMult(PK_i, challenge * lambda_i)

  return l == r
~~~

The Coordinator can verify each signature share before first aggregating and verifying the
signature under the group public key. However, since the aggregate signature is valid if
all signature shares are valid, this order of operations is more expensive if the
signature is valid.

## Identifiable Abort {#abort}

FROST does not provide robustness; i.e, all participants are required to complete the
protocol honestly in order to generate a valid signature. When the signing protocol
does not produce a valid signature, the Coordinator SHOULD abort; see {{sec-considerations}}
for more information about FROST's security properties and the threat model.

As a result of this property, a misbehaving participant can cause a denial-of-service on
the signing protocol by contributing malformed signature shares or refusing to participate.
Identifying misbehaving participants that produce invalid shares can be done by checking
signature shares from each participant using `verify_signature_share` as described in {{frost-aggregation}}.
FROST assumes the network channel is authenticated to identify which signer misbehaved.
FROST allows for identifying misbehaving participants that produce invalid signature shares
as described in {{frost-aggregation}}. FROST does not provide accommodations for identifying
participants that refuse to participate, though applications are assumed to detect when participants
fail to engage in the signing protocol.

In both cases, preventing this type of attack requires the Coordinator to identify
misbehaving participants such that applications can take corrective action. The mechanism
for acting on misbehaving participants is out of scope for this specification. However,
one reasonable approach would be to remove the misbehaving participant from the set of allowed
participants in future runs of FROST.

# Ciphersuites {#ciphersuites}

A FROST ciphersuite must specify the underlying prime-order group details
and cryptographic hash function. Each ciphersuite is denoted as (Group, Hash),
e.g., (ristretto255, SHA-512). This section contains some ciphersuites.
Each ciphersuite also includes a context string, denoted `contextString`,
which is an ASCII string literal (with no NULL terminating character).

The RECOMMENDED ciphersuite is (ristretto255, SHA-512) as described in {{recommended-suite}}.
The (Ed25519, SHA-512) and (Ed448, SHAKE256) ciphersuites are included
for compatibility with Ed25519 and Ed448 as defined in {{!RFC8032}}.

The DeserializeElement and DeserializeScalar functions instantiated for a
particular prime-order group corresponding to a ciphersuite MUST adhere
to the description in {{dep-pog}}. Validation steps for these functions
are described for each of the ciphersuites below. Future ciphersuites MUST
describe how input validation is done for DeserializeElement and DeserializeScalar.

Each ciphersuite includes explicit instructions for verifying signatures produced
by FROST. Note that these instructions are equivalent to those produced by a single
participant.

Each ciphersuite adheres to the requirements in {{ciphersuite-reqs}}. Future
ciphersuites MUST also adhere to these requirements.

## FROST(Ed25519, SHA-512)

This ciphersuite uses edwards25519 for the Group and SHA-512 for the Hash function `H`
meant to produce Ed25519-compliant signatures as specified in {{Section 5.1 of !RFC8032}}.
The value of the contextString parameter is "FROST-ED25519-SHA512-v11".

- Group: edwards25519 {{!RFC8032}}, where Ne = 32 and Ns = 32.
  - Order(): Return 2^252 + 27742317777372353535851937790883648493 (see {{?RFC7748}}).
  - Identity(): As defined in {{RFC7748}}.
  - RandomScalar(): Implemented by returning a uniformly random Scalar in the range
    \[0, `G.Order()` - 1\]. Refer to {{random-scalar}} for implementation guidance.
  - SerializeElement(A): Implemented as specified in {{!RFC8032, Section 5.1.2}}.
    Additionally, this function validates that the input element is not the group
    identity element.
  - DeserializeElement(buf): Implemented as specified in {{!RFC8032, Section 5.1.3}}.
    Additionally, this function validates that the resulting element is not the group
    identity element and is in the prime-order subgroup. If any of these checks fail,
    deserialization returns an error. The latter check can
    be implemented by multiplying the resulting point by the order of the group and
    checking that the result is the identity element. Note that optimizations for
    this check exist; see {{Pornin22}}.
  - SerializeScalar(s): Implemented by outputting the little-endian 32-byte encoding of
    the Scalar value with the top three bits set to zero.
  - DeserializeScalar(buf): Implemented by attempting to deserialize a Scalar from a
    little-endian 32-byte string. This function can fail if the input does not
    represent a Scalar in the range \[0, `G.Order()` - 1\]. Note that this means the
    top three bits of the input MUST be zero.

- Hash (`H`): SHA-512, which has 64 bytes of output
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


Normally H2 would also include a domain separator, but for compatibility with {{!RFC8032}}, it is omitted.

Signature verification is as specified in {{Section 5.1.7 of RFC8032}} with the
constraint that implementations MUST check the group equation `[8][z]B = [8]R + [8][c]PK`
(changed to use the notation in this document).

Canonical signature encoding is as specified in {{sig-encoding}}.

## FROST(ristretto255, SHA-512) {#recommended-suite}

This ciphersuite uses ristretto255 for the Group and SHA-512 for the Hash function `H`.
The value of the contextString parameter is "FROST-RISTRETTO255-SHA512-v11".

- Group: ristretto255 {{!RISTRETTO=I-D.irtf-cfrg-ristretto255-decaf448}},
  where Ne = 32 and Ns = 32.
  - Order(): Return 2^252 + 27742317777372353535851937790883648493 (see {{RISTRETTO}}).
  - Identity(): As defined in {{RISTRETTO}}.
  - RandomScalar(): Implemented by returning a uniformly random Scalar in the range
    \[0, `G.Order()` - 1\]. Refer to {{random-scalar}} for implementation guidance.
  - SerializeElement(A): Implemented using the 'Encode' function from {{!RISTRETTO}}.
    Additionally, this function validates that the input element is not the group
    identity element.
  - DeserializeElement(buf): Implemented using the 'Decode' function from {{!RISTRETTO}}.
    Additionally, this function validates that the resulting element is not the group
    identity element. If either 'Decode' or that check fails, deserialization returns an error.
  - SerializeScalar(s): Implemented by outputting the little-endian 32-byte encoding of
    the Scalar value with the top three bits set to zero.
  - DeserializeScalar(buf): Implemented by attempting to deserialize a Scalar from a
    little-endian 32-byte string. This function can fail if the input does not
    represent a Scalar in the range \[0, `G.Order()` - 1\]. Note that this means the
    top three bits of the input MUST be zero.

- Hash (`H`): SHA-512, which has 64 bytes of output
  - H1(m): Implemented by computing H(contextString || "rho" || m) and mapping the
    output to a Scalar as described in {{!RISTRETTO, Section 4.4}}.
  - H2(m): Implemented by computing H(contextString || "chal" || m) and mapping the
    output to a Scalar as described in {{!RISTRETTO, Section 4.4}}.
  - H3(m): Implemented by computing H(contextString \|\| "nonce" \|\| m) and mapping the
    output to a Scalar as described in {{!RISTRETTO, Section 4.4}}.
  - H4(m): Implemented by computing H(contextString \|\| "msg" \|\| m).
  - H5(m): Implemented by computing H(contextString \|\| "com" \|\| m).

Signature verification is as specified in {{prime-order-verify}}.

Canonical signature encoding is as specified in {{sig-encoding}}.

## FROST(Ed448, SHAKE256)

This ciphersuite uses edwards448 for the Group and SHAKE256 for the Hash function `H`
meant to produce Ed448-compliant signatures as specified in {{Section 5.2 of RFC8032}}. Note that this
ciphersuite does not allow applications to specify a context string as is allowed for Ed448
in {{RFC8032}}, and always sets the {{RFC8032}} context string to the empty string.
The value of the (internal to FROST) contextString parameter is "FROST-ED448-SHAKE256-v11".

- Group: edwards448 {{!RFC8032}}, where Ne = 57 and Ns = 57.
  - Order(): Return 2^446 - 13818066809895115352007386748515426880336692474882178609894547503885.
  - Identity(): As defined in {{RFC7748}}.
  - RandomScalar(): Implemented by returning a uniformly random Scalar in the range
    \[0, `G.Order()` - 1\]. Refer to {{random-scalar}} for implementation guidance.
  - SerializeElement(A): Implemented as specified in {{!RFC8032, Section 5.2.2}}.
    Additionally, this function validates that the input element is not the group
    identity element.
  - DeserializeElement(buf): Implemented as specified in {{!RFC8032, Section 5.2.3}}.
    Additionally, this function validates that the resulting element is not the group
    identity element and is in the prime-order subgroup. If any of these checks fail,
    deserialization returns an error. The latter check can
    be implemented by multiplying the resulting point by the order of the group and
    checking that the result is the identity element. Note that optimizations for
    this check exist; see {{Pornin22}}.
  - SerializeScalar(s): Implemented by outputting the little-endian 57-byte encoding of
    the Scalar value.
  - DeserializeScalar(buf): Implemented by attempting to deserialize a Scalar from a
    little-endian 57-byte string. This function can fail if the input does not
    represent a Scalar in the range \[0, `G.Order()` - 1\].

- Hash (`H`): SHAKE256 with 114 bytes of output
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

Normally H2 would also include a domain separator, but for compatibility with {{!RFC8032}}, it is omitted.

Signature verification is as specified in {{Section 5.2.7 of RFC8032}} with the
constraint that implementations MUST check the group equation `[4][z]B = [4]R + [4][c]PK`
(changed to use the notation in this document).

Canonical signature encoding is as specified in {{sig-encoding}}.

## FROST(P-256, SHA-256)

This ciphersuite uses P-256 for the Group and SHA-256 for the Hash function `H`.
The value of the contextString parameter is "FROST-P256-SHA256-v11".

- Group: P-256 (secp256r1) {{x9.62}}, where Ne = 33 and Ns = 32.
  - Order(): Return 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551.
  - Identity(): As defined in {{x9.62}}.
  - RandomScalar(): Implemented by returning a uniformly random Scalar in the range
    \[0, `G.Order()` - 1\]. Refer to {{random-scalar}} for implementation guidance.
  - SerializeElement(A): Implemented using the compressed Elliptic-Curve-Point-to-Octet-String
    method according to {{SEC1}}, yielding a 33-byte output. Additionally, this function validates
    that the input element is not the group identity element.
  - DeserializeElement(buf): Implemented by attempting to deserialize a 33-byte input string to
    a public key using the compressed Octet-String-to-Elliptic-Curve-Point method according to {{SEC1}},
    and then performs public-key validation as defined in section 3.2.2.1 of {{SEC1}}.
    This includes checking that the coordinates of the resulting point are
    in the correct range, that the point is on the curve, and that the point is not
    the point at infinity. (As noted in the specification, validation of the point
    order is not required since the cofactor is 1.) If any of these checks fail,
    deserialization returns an error.
  - SerializeScalar(s): Implemented using the Field-Element-to-Octet-String conversion
    according to {{SEC1}}.
  - DeserializeScalar(buf): Implemented by attempting to deserialize a Scalar from a 32-byte
    string using Octet-String-to-Field-Element from {{SEC1}}. This function can fail if the
    input does not represent a Scalar in the range \[0, `G.Order()` - 1\].

- Hash (`H`): SHA-256, which has 32 bytes of output
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

Canonical signature encoding is as specified in {{sig-encoding}}.

## FROST(secp256k1, SHA-256)

This ciphersuite uses secp256k1 for the Group and SHA-256 for the Hash function `H`.
The value of the contextString parameter is "FROST-secp256k1-SHA256-v11".

- Group: secp256k1 {{SEC2}}, where Ne = 33 and Ns = 32.
  - Order(): Return 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141.
  - Identity(): As defined in {{SEC2}}.
  - RandomScalar(): Implemented by returning a uniformly random Scalar in the range
    \[0, `G.Order()` - 1\]. Refer to {{random-scalar}} for implementation guidance.
  - SerializeElement(A): Implemented using the compressed Elliptic-Curve-Point-to-Octet-String
    method according to {{SEC1}}, yielding a 33-byte output. Additionally, this function validates
    that the input element is not the group identity element.
  - DeserializeElement(buf): Implemented by attempting to deserialize a 33-byte input string to
    a public key using the compressed Octet-String-to-Elliptic-Curve-Point method according to {{SEC1}},
    and then performs public-key validation as defined in section 3.2.2.1 of {{SEC1}}.
    This includes checking that the coordinates of the resulting point are
    in the correct range, that the point is on the curve, and that the point is not
    the point at infinity. (As noted in the specification, validation of the point
    order is not required since the cofactor is 1.) If any of these checks fail,
    deserialization returns an error.
  - SerializeScalar(s): Implemented using the Field-Element-to-Octet-String conversion
    according to {{SEC1}}.
  - DeserializeScalar(buf): Implemented by attempting to deserialize a Scalar from a 32-byte
    string using Octet-String-to-Field-Element from {{SEC1}}. This function can fail if the
    input does not represent a Scalar in the range \[0, `G.Order()` - 1\].

- Hash (`H`): SHA-256, which has 32 bytes of output
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

Canonical signature encoding is as specified in {{sig-encoding}}.

## Ciphersuite Requirements {#ciphersuite-reqs}

Future documents that introduce new ciphersuites MUST adhere to
the following requirements.

1. H1, H2, and H3 all have output distributions that are close to
  (indistinguishable from) the uniform distribution.
2. All hash functions MUST be domain separated with a per-suite context
  string. Note that the FROST(Ed25519, SHA-512) ciphersuite does not
  adhere to this requirement for H2 alone to maintain compatibility
  with {{RFC8032}}.
3. The group MUST be of prime-order, and all deserialization functions MUST
  output elements that belong to their respective sets of Elements or Scalars,
  or failure when deserialization fails.
4. The canonical signature encoding details are clearly specified.

# Security Considerations {#sec-considerations}

A security analysis of FROST exists in {{FROST20}} and {{StrongerSec22}}. At a high
level, FROST provides security against Existential Unforgeability Under Chosen Message
Attack (EUF-CMA) attacks, as defined in {{StrongerSec22}}. Satisfying this requirement
requires the ciphersuite to adhere to the requirements in {{ciphersuite-reqs}}, as well
as the following assumptions to hold.

* The signer key shares are generated and distributed securely, e.g., via a trusted dealer
that performs key generation (see {{dep-vss}}) or through a distributed key generation protocol.
* The Coordinator and at most `(MIN_PARTICIPANTS-1)` participants may be corrupted.

Note that the Coordinator is not trusted with any private information and communication
at the time of signing can be performed over a public channel, as long as it is
authenticated and reliable.

FROST provides security against denial of service attacks under the following assumptions:

* The Coordinator does not perform a denial of service attack.
* The Coordinator identifies misbehaving participants such that they can be removed from
  future invocations of FROST. The Coordinator may also abort upon detecting a misbehaving
  participant to ensure that invalid signatures are not produced.

FROST does not aim to achieve the following goals:

* Post-quantum security. FROST, like plain Schnorr signatures, requires the hardness of the Discrete Logarithm Problem.
* Robustness. Preventing denial-of-service attacks against misbehaving participants requires the Coordinator
  to identify and act on misbehaving participants; see {{abort}} for more information. While FROST
  does not provide robustness, {{ROAST}} is as a wrapper protocol around FROST that does.
* Downgrade prevention. All participants in the protocol are assumed to agree on what algorithms to use.
* Metadata protection. If protection for metadata is desired, a higher-level communication
channel can be used to facilitate key generation and signing.

The rest of this section documents issues particular to implementations or deployments.

## Side-channel mitigations

Several routines process secret values (nonces, signing keys / shares), and depending
on the implementation and deployment environment, mitigating side-channels may be
pertinent. Mitigating these side-channels requires implementing `G.ScalarMult()`, `G.ScalarBaseMult()`,
`G.SerializeScalar()`, and `G.DeserializeScalar()` in constant (value-independent) time.
The various ciphersuites lend themselves differently to specific implementation techniques
and ease of achieving side-channel resistance, though ultimately avoiding value-dependent
computation or branching is the goal.

## Optimizations

{{StrongerSec22}} presented an optimization to FROST that reduces the total number of scalar multiplications
from linear in the number of signing participants to a constant. However, as described in {{StrongerSec22}},
this optimization removes the guarantee that the set of signer participants that started round one of
the protocol is the same set of signing participants that produced the signature output by round two.
As such, the optimization is NOT RECOMENDED, and it is not covered in this document.

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
level commensurate with the security inherent to the ciphersuite chosen. It is
RECOMMENDED that applications which choose to apply pre-hashing use the hash function
(`H`) associated with the chosen ciphersuite in a manner similar to how `H4` is defined.
In particular, a different prefix SHOULD be used to differentiate this pre-hash from
`H4`. For example, if a fictional protocol Quux decided to pre-hash its input messages,
one possible way to do so is via `H(contextString || "Quux-pre-hash" || m)`.

## Input Message Validation {#message-validation}

Message validation varies by application. For example, some applications may
require that participants only process messages of a certain structure. In digital
currency applications, wherein multiple participants may collectively sign a transaction,
it is reasonable to require that each participant check the input message to be a
syntactically valid transaction.

As another example, some applications may require that participants only process
messages with permitted content according to some policy. In digital currency
applications, this might mean that a transaction being signed is allowed and
intended by the relevant stakeholders. Another instance of this type of message
validation is in the context of {{?TLS=RFC8446}}, wherein implementations may
use threshold signing protocols to produce signatures of transcript hashes. In
this setting, signing participants might require the raw TLS handshake messages
to validate before computing the transcript hash that is signed.

In general, input message validation is an application-specific consideration
that varies based on the use case and threat model. However, it is RECOMMENDED
that applications take additional precautions and validate inputs so that
participants do not operate as signing oracles for arbitrary messages.

# IANA Considerations

This document makes no IANA requests.

--- back

# Acknowledgments

This document was improved based on input and contributions by the Zcash Foundation engineering team.
In addition, the authors of this document would like to thank
Isis Lovecruft,
Alden Torres,
T. Wilson-Brown,
and Conrado Gouvea
for their inputs and contributions.

# Schnorr Signature Encoding {#sig-encoding}

This section describes one possible canonical encoding of FROST signatures. Using notation
from {{Section 3 of TLS}}, the encoding of a FROST signature (R, z) is as follows:

~~~
  struct {
    opaque R_encoded[Ne];
    opaque z_encoded[Ns];
  } Signature;
~~~

Where Signature.R_encoded is `G.SerializeElement(R)` and Signature.z_encoded is
`G.SerializeScalar(z)` and `G` is determined by ciphersuite.

# Schnorr Signature Generation and Verification for Prime-Order Groups {#prime-order-verify}

This section contains descriptions of functions for generating and verifying Schnorr signatures.
It is included to complement the routines present in {{RFC8032}} for prime-order groups, including
ristretto255, P-256, and secp256k1. The functions for generating and verifying signatures are
`prime_order_sign` and `prime_order_verify`, respectively.

The function `prime_order_sign` produces a Schnorr signature over a message given a full secret signing
key as input (as opposed to a key share.)

~~~
Inputs:
- msg, message to sign, a byte string.
- sk, secret key, a Scalar.

Outputs:
- (R, z), a Schnorr signature consisting of an Element R and
  Scalar z.

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
Inputs:
- msg, signed message, a byte string.
- sig, a tuple (R, z) output from signature generation.
- PK, public key, an Element.

Outputs:
- True if signature is valid, and False otherwise.

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
Secret Sharing {{?ShamirSecretSharing=DOI.10.1145/359168.359176}}, as described in {{dep-shamir}} and {{dep-vss}} to create secret
shares of s, denoted `s_i` for `i = 1, ..., MAX_PARTICIPANTS`, to be sent to all `MAX_PARTICIPANTS` participants.
This operation is specified in the `trusted_dealer_keygen` algorithm. The mathematical relation
between the secret key `s` and the `MAX_PARTICIPANTS` secret shares is formalized in the `secret_share_combine(shares)`
algorithm, defined in {{dep-shamir}}.

The dealer that performs `trusted_dealer_keygen` is trusted to 1) generate good randomness, and 2) delete secret values after distributing shares to each participant, and 3) keep secret values confidential.

~~~
Inputs:
- secret_key, a group secret, a Scalar, that MUST be derived from at
  least Ns bytes of entropy.
- MAX_PARTICIPANTS, the number of shares to generate, an integer.
- MIN_PARTICIPANTS, the threshold of the secret sharing scheme,
  an integer.

Outputs:
- participant_private_keys, MAX_PARTICIPANTS shares of the secret
  key s, each a tuple consisting of the participant identifier
  (a NonZeroScalar) and the key share (a Scalar).
- group_public_key, public key corresponding to the group signing
  key, an Element.
- vss_commitment, a vector commitment of Elements in G, to each of
  the coefficients in the polynomial defined by secret_key_shares and
  whose first element is G.ScalarBaseMult(s).

def trusted_dealer_keygen(
        secret_key, MAX_PARTICIPANTS, MIN_PARTICIPANTS):
  # Generate random coefficients for the polynomial
  coefficients = []
  for i in range(0, MIN_PARTICIPANTS - 1):
    coefficients.append(G.RandomScalar())
  participant_private_keys, coefficients = secret_share_shard(
      secret_key, coefficients, MAX_PARTICIPANTS)
  vss_commitment = vss_commit(coefficients):
  return participant_private_keys, vss_commitment[0], vss_commitment
~~~

It is assumed the dealer then sends one secret key share to each of the `NUM_PARTICIPANTS` participants, along with `vss_commitment`.
After receiving their secret key share and `vss_commitment`, participants MUST abort if they do not have the same view of `vss_commitment`.
The dealer can use a secure broadcast channel to ensure each participant has a consistent view of this commitment.
Furthermore, each participant MUST perform `vss_verify(secret_key_share_i, vss_commitment)`, and abort if the check fails.
The trusted dealer MUST delete the secret_key and secret_key_shares upon completion.

Use of this method for key generation requires a mutually authenticated secure channel
between the dealer and participants to send secret key shares, wherein the channel provides confidentiality
and integrity. Mutually authenticated TLS is one possible deployment option.

## Shamir Secret Sharing {#dep-shamir}

In Shamir secret sharing, a dealer distributes a secret `Scalar` `s` to `n` participants
in such a way that any cooperating subset of at least `MIN_PARTICIPANTS` participants can recover the
secret. There are two basic steps in this scheme: (1) splitting a secret into
multiple shares, and (2) combining shares to reveal the resulting secret.

This secret sharing scheme works over any field `F`. In this specification, `F` is
the scalar field of the prime-order group `G`.

The procedure for splitting a secret into shares is as follows.
The algorithm `polynomial_evaluate` is defined in {{dep-extended-polynomial-operations}}.

~~~
Inputs:
- s, secret value to be shared, a Scalar.
- coefficients, an array of size MIN_PARTICIPANTS - 1 with randomly
  generated Scalars, not including the 0th coefficient of the
  polynomial.
- MAX_PARTICIPANTS, the number of shares to generate, an integer less
  than 2^16.

Outputs:
- secret_key_shares, A list of MAX_PARTICIPANTS number of secret
  shares, each a tuple consisting of the participant identifier
  (a NonZeroScalar) and the key share (a Scalar).
- coefficients, a vector of MIN_PARTICIPANTS coefficients which
  uniquely determine a polynomial f.

def secret_share_shard(s, coefficients, MAX_PARTICIPANTS):
  # Prepend the secret to the coefficients
  coefficients = [s] + coefficients

  # Evaluate the polynomial for each point x=1,...,n
  secret_key_shares = []
  for x_i in range(1, MAX_PARTICIPANTS + 1):
    y_i = polynomial_evaluate(Scalar(x_i), coefficients)
    secret_key_share_i = (x_i, y_i)
    secret_key_shares.append(secret_key_share_i)
  return secret_key_shares, coefficients
~~~

Let `points` be the output of this function. The i-th element in `points` is
the share for the i-th participant, which is the randomly generated polynomial
evaluated at coordinate `i`. We denote a secret share as the tuple `(i, points[i])`,
and the list of these shares as `shares`. `i` MUST never equal `0`; recall that
`f(0) = s`, where `f` is the polynomial defined in a Shamir secret sharing operation.

The procedure for combining a `shares` list of length `MIN_PARTICIPANTS` to recover the
secret `s` is as follows; the algorithm `polynomial_interpolate_constant` is defined in {{dep-extended-polynomial-operations}}.

~~~
Inputs:
- shares, a list of at minimum MIN_PARTICIPANTS secret shares, each a
  tuple (i, f(i)) where i and f(i) are Scalars.

Outputs:
- s, the resulting secret that was previously split into shares,
  a Scalar.

Errors:
- "invalid parameters", if fewer than MIN_PARTICIPANTS input shares
  are provided.

def secret_share_combine(shares):
  if len(shares) < MIN_PARTICIPANTS:
    raise "invalid parameters"
  s = polynomial_interpolate_constant(shares)
  return s
~~~

### Additional polynomial operations  {#dep-extended-polynomial-operations}

This section describes two functions. One function, denoted `polynomial_evaluate`,
is for evaluating a polynomial `f(x)` at a particular point `x` using Horner's method,
i.e., computing `y = f(x)`. The other function, `polynomial_interpolate_constant`, is for
recovering the constant term of an interpolating polynomial defined by a set of points.

The function `polynomial_evaluate` is defined as follows.

~~~
Inputs:
- x, input at which to evaluate the polynomial, a Scalar
- coeffs, the polynomial coefficients, a list of Scalars

Outputs: Scalar result of the polynomial evaluated at input x

def polynomial_evaluate(x, coeffs):
  value = Scalar(0)
  for coeff in reverse(coeffs):
    value *= x
    value += coeff
  return value
~~~

The function `polynomial_interpolate_constant` is defined as follows.

~~~
Inputs:
- points, a set of t points with distinct x coordinates on
  a polynomial f, each a tuple of two Scalar values representing the
  x and y coordinates.

Outputs:
- f_zero, the constant term of f, i.e., f(0), a Scalar.

def polynomial_interpolate_constant(points):
  x_coords = []
  for (x, y) in points:
    x_coords.append(x)

  f_zero = Scalar(0)
  for (x, y) in points:
    delta = y * derive_interpolating_value(x_coords, x)
    f_zero += delta

  return f_zero
~~~

## Verifiable Secret Sharing {#dep-vss}

Feldman's Verifiable Secret Sharing (VSS) {{?FeldmanSecretSharing=DOI.10.1109/SFCS.1987.4}}
builds upon Shamir secret sharing, adding a verification step to demonstrate the consistency of a participant's
share with a public commitment to the polynomial `f` for which the secret `s`
is the constant term. This check ensures that all participants have a point
(their share) on the same polynomial, ensuring that they can later reconstruct
the correct secret.

The procedure for committing to a polynomial `f` of degree at most `MIN_PARTICIPANTS-1` is as follows.

~~~
Inputs:
- coeffs, a vector of the MIN_PARTICIPANTS coefficients which
  uniquely determine a polynomial f.

Outputs:
- vss_commitment, a vector commitment to each of the coefficients in
  coeffs, where each item of the vector commitment is an Element.

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
Inputs:
- share_i: A tuple of the form (i, sk_i), where i indicates the
  participant identifier (a NonZeroScalar), and sk_i the
  participant's secret key, a secret share of the constant term of f,
  where sk_i is a Scalar.
- vss_commitment, a VSS commitment to a secret polynomial f, a vector
  commitment to each of the coefficients in coeffs, where each
  element of the vector commitment is an Element.

Outputs:
- True if sk_i is valid, and False otherwise.

def vss_verify(share_i, vss_commitment)
  (i, sk_i) = share_i
  S_i = G.ScalarBaseMult(sk_i)
  S_i' = G.Identity()
  for j in range(0, MIN_PARTICIPANTS):
    S_i' += G.ScalarMult(vss_commitment[j], pow(i, j))
  return S_i == S_i'
~~~

We now define how the Coordinator and participants can derive group info,
which is an input into the FROST signing protocol.

~~~
Inputs:
- MAX_PARTICIPANTS, the number of shares to generate, an integer.
- MIN_PARTICIPANTS, the threshold of the secret sharing scheme,
  an integer.
- vss_commitment, a VSS commitment to a secret polynomial f, a vector
  commitment to each of the coefficients in coeffs, where each
  element of the vector commitment is an Element.

Outputs:
- PK, the public key representing the group, an Element.
- participant_public_keys, a list of MAX_PARTICIPANTS public keys
  PK_i for i=1,...,MAX_PARTICIPANTS, where each PK_i is the public
  key, an Element, for participant i.

def derive_group_info(MAX_PARTICIPANTS, MIN_PARTICIPANTS, vss_commitment)
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
such that |p - 2<sup>b</sup>| is less than 2<sup>(b/2)</sup>, then
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
  in the protocol, identified by their NonZeroScalar identifier, and for each participant:
  the hiding and binding commitment values produced in {{frost-round-one}}; the randomness
  values used to derive the commitment nonces in `nonce_generate`; the resulting group
  binding factor input computed in part from the group commitment list encoded as
  described in {{dep-encoding}}; and group binding factor as computed in {{frost-round-two}}).
- Round two parameters and outputs. This lists the NUM_PARTICIPANTS participants engaged
  in the protocol, identified by their NonZeroScalar identifier, along with their corresponding
  output signature share as produced in {{frost-round-two}}.
- Final output. This lists the aggregate signature as produced in {{frost-aggregation}}.


## FROST(Ed25519, SHA-512)

~~~
// Configuration information
MAX_PARTICIPANTS: 3
MIN_PARTICIPANTS: 2
NUM_PARTICIPANTS: 2

// Group input parameters
participant_list: 1,3
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

// Signer round one outputs
P1 hiding_nonce_randomness: ededfd1e5661d1e8ae2fbc4182c9e3d0296433cc0
fccfc4634eff384ff5b60d1
P1 binding_nonce_randomness: 38faea169d8faaa201390c6ddfdf18b374d7cc7a
8d649d718f7e950e29f8cbda
P1 hiding_nonce: 8513f1413a3fe949e1061dba46fc1f1a148914c5dd76d7fc16ee
357fad65cc0e
P1 binding_nonce: b1ca00e1fdd13e8a7df56719e53e4a457619244b63de4588e12
189d13f99280c
P1 hiding_nonce_commitment: cd745f9f0be7afae8fc4036d79b35448ad73be3af
ea863e74fb1f1ac734bab4f
P1 binding_nonce_commitment: a2eab6037ce18f1bc65fbb9de41309a428f6233c
99bccb0c95655a8cd8c0a707
P1 binding_factor_input: c5b95020cba31a9035835f074f718d0c3af02a318d6b
4723bbd1c088f4889dd7b9ff8e79f9a67a9d27605144259a7af18b7cca2539ffa5c4f
1366a98645da8f49fb6a22408875bf078b99322b7e2395abc1e88698a4ee9da44a705
5b9b527c06a72956ff49d8a3e7490ff737de1377d86da9e0da28e566063127a3619d7
5ef340100000000000000000000000000000000000000000000000000000000000000
P1 binding_factor: 715d02ce9a20023118a1d064a0349f70e9baeda5c0137b29ad
9cc9e1c032d503
P3 hiding_nonce_randomness: b56c9f60335566fa0760700d3d4d97654493a219f
979842523fb5f0d6e69c21c
P3 binding_nonce_randomness: de2d61a4e15e7eeb80dc586437976be7e575fb90
f1a9d49bd3275a2da837b194
P3 hiding_nonce: c9d07e00a260957a9207144f3a1d03fad3122a26fe645d2c7088
6c7730064606
P3 binding_nonce: ae3777ef20bf8b7b5673d79a8fd0ad240efe130a599d053fc5e
8770bb14b3c0b
P3 hiding_nonce_commitment: fe152c2075a568f5bacf92f292b71c84c213f04b6
0d36b1d1a68036cb3f13f98
P3 binding_nonce_commitment: 67cc046fc46a8af6304e67d13c080c89fd651889
417f324019bf135fd49e2497
P3 binding_factor_input: c5b95020cba31a9035835f074f718d0c3af02a318d6b
4723bbd1c088f4889dd7b9ff8e79f9a67a9d27605144259a7af18b7cca2539ffa5c4f
1366a98645da8f49fb6a22408875bf078b99322b7e2395abc1e88698a4ee9da44a705
5b9b527c06a72956ff49d8a3e7490ff737de1377d86da9e0da28e566063127a3619d7
5ef340300000000000000000000000000000000000000000000000000000000000000
P3 binding_factor: 422ec5166de43c17781ba2620b184b8d3b38f7b5a750aa38f1
8ca8ee9171c901

// Signer round two outputs
P1 sig_share: 0350317b0ebd59d2875bec521055bbc8bdf884b2918c9e917222ecf
8404c0f0e
P3 sig_share: 5df461a778e99c362d5871578b398b2296159b0fa8fee633e5e9f93
f0a7c5b02

sig: c364491515047d220533cb331cf9e1dee2c6dc1df96d3c7c0d3644db97fc9ba3
73709dc56c43e4b0de166607bd9467d6530e20c2398b85c5570ce6384bc86a00
~~~

## FROST(Ed448, SHAKE256)

~~~
// Configuration information
MAX_PARTICIPANTS: 3
MIN_PARTICIPANTS: 2
NUM_PARTICIPANTS: 2

// Group input parameters
participant_list: 1,3
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

// Signer round one outputs
P1 hiding_nonce_randomness: 4331d9e045e8b51789594bc7430cc3ac5bfeb07c3
46895830462d27afd13edf2
P1 binding_nonce_randomness: de3ffdea149fcf48ec772609f864480b69767d48
bd82d15771b64b7991d2129a
P1 hiding_nonce: f1c1b2063cb90351f80f967c668780a06ece8ccddb8bdf91da90
991551c24ef9ff51bcbecb92eff7e875e85adcefa22eb5b2d53ba2eb381100
P1 binding_nonce: f92917f8169dcf524104d5d1f645e9b76702e9b036ab776c415
1c35c1fff820eebb1856410fe6aa4cc9765759e9663fa9e5a60d67d683a3000
P1 hiding_nonce_commitment: 86ac0537275f2be903660d1a450e23ffa4c31fc4a
e35e8b511d066410a925f2d252a31f1f30a9bf2726d1968ddd2a78b7d316332c4c9b1
4b00
P1 binding_nonce_commitment: 38cb263362cb86142c3e3c5cc0a6722ea89a38d4
225093dbad376c4813ab2e29a938f627449767700338d72613d8b9e5b474f01a9f163
96980
P1 binding_factor_input: 106dadce87ca867018702d69a02effd165e1ac1a511c
957cff1897ceff2e34ca212fe798d84f0bde6054bf0fa77fd4cd4bc4853d6dc8dbd19
d340923f0ebbbb35172df4ab865a45d55af31fa0e6606ea97cf8513022b2b133d0f9f
6b8d3be184221fc4592bf12bd7fb4127bb67e51a6dc9e592b408af12c7bd0a3a910f5
e530f86379ed25f8af0c77bc8768cc2e511575c53ad94335c42ccbd7d64b6516345ff
a0199ef184e74aa04367abefc5d2e912f332daf4718152ca6fa9889eea7ffb312f269
9a51cce6a5dd88cdb92f80118d2338f2d1bc8c73b90295646f4b8f9a62fb77339a401
000000000000000000000000000000000000000000000000000000000000000000000
0000000000000000000000000000000000000000000
P1 binding_factor: eb3bfe2a0774acfa549e081f3adc252d2cbc92d996ff6cdff6
482ad363c7888b0e8bfd47a2a0cb158b2de1726fd70a3ed3749635aa4a560a00
P3 hiding_nonce_randomness: e2389426026d53848971c03ccfc60d028812951d1
807f7c19ab5d2ec5b2c75d4
P3 binding_nonce_randomness: e1d692e498bb451093c08d1c9bb374a8c776b336
e5aeda289769213e1d8615c3
P3 hiding_nonce: a11f4bed1e4a26df4577709f826f427f4103e2bfeebfa4ad5c7a
6b515381953cd06c2d01c2be75420f23447fd2f36bc8a6e0c34f3efbc42d00
P3 binding_nonce: 5383eebf92663285592d5da40e5d77174ca1ca3329cdc21ae62
9323326386fecdf2029e3b9845f0d3be20e20d479e1148511be3268c3363900
P3 hiding_nonce_commitment: d7e281bc9780884e113cbe96d30e053715cadb8a4
49ea1d6b2cd86d85a146c023be53d893dd6cfa39ce6c5d4896d38bdf706521b71a38d
3c00
P3 binding_nonce_commitment: c3e27658c3a40ee4784fff1204269c454307bbef
b9f797e39ad0915256389d5aa12b4d4f79e619f20b5ec032ece8dfa6245a8d77900e1
07480
P3 binding_factor_input: 106dadce87ca867018702d69a02effd165e1ac1a511c
957cff1897ceff2e34ca212fe798d84f0bde6054bf0fa77fd4cd4bc4853d6dc8dbd19
d340923f0ebbbb35172df4ab865a45d55af31fa0e6606ea97cf8513022b2b133d0f9f
6b8d3be184221fc4592bf12bd7fb4127bb67e51a6dc9e592b408af12c7bd0a3a910f5
e530f86379ed25f8af0c77bc8768cc2e511575c53ad94335c42ccbd7d64b6516345ff
a0199ef184e74aa04367abefc5d2e912f332daf4718152ca6fa9889eea7ffb312f269
9a51cce6a5dd88cdb92f80118d2338f2d1bc8c73b90295646f4b8f9a62fb77339a403
000000000000000000000000000000000000000000000000000000000000000000000
0000000000000000000000000000000000000000000
P3 binding_factor: ce5b4d16d063ef90a4ae283150f31f6f050d31a0fb6693d238
d06c0f9f0c0c9d60d0c9e3b64b52c005187f4d1bc41b72125599a7fe67401f00

// Signer round two outputs
P1 sig_share: 1dff7d5776809e6e2cf3d44edd68334715efee066a5e6c574759360
ec6423b061003ef5c0f81c9409320b654f112cbc3b26a71c23f2e750b00
P3 sig_share: c6839bc091e8505d8df843fa2d768cd877a6b4531eabd00a024aeae
3ff01a1d26da9b923f7846856c240496178e084bbe1180749f255891500

sig: 56dfd8851fcaf5e56cc3a4243135b863d16a5735238f825d72a98db822af247e
59585c6f6ad5728ece5a50799ec934014c23399a989dd28f80e38219180869efcbb9e
b18490bdfbf1f8d95a35a88093d6249a320f2c544dcd87daca880060632975561ffb5
69f34f7f9483780b3284fe2000
~~~

## FROST(ristretto255, SHA-512)

~~~
// Configuration information
MAX_PARTICIPANTS: 3
MIN_PARTICIPANTS: 2
NUM_PARTICIPANTS: 2

// Group input parameters
participant_list: 1,3
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

// Signer round one outputs
P1 hiding_nonce_randomness: 92e6aa742604eb7fae638551ef20e0a2d4174d0ff
2046cacc9dbd21546f52e14
P1 binding_nonce_randomness: b91611b8c61d57b726e387c9a9ad0e9ee7877529
2049df8cf06286865a309d49
P1 hiding_nonce: aefa609db4c4515c31bd60d9d677d91726bdeea37a1407c15a41
6f0c7c635d0c
P1 binding_nonce: 0521526aa795060587419340a3fc69ce155410abecdc23f9d49
8eb401e6ae10f
P1 hiding_nonce_commitment: da84ab8951dadd8b17de6ef2195f0f21636bc99c4
d1057f1732b1256da032e34
P1 binding_nonce_commitment: e88138037c02b943b55327ec49c8feb5addd4628
27783c379988efdaac7b350d
P1 binding_factor_input: 9c245d5fc2e451c5c5a617cc6f2a20629fb317d9b1c1
915ab4bfa319d4ebf922c54dd1a5b3b754550c72734ac9255db8107a2b01f361754d9
f13f428c2f6de9ed98771b7e34d27c1ecc1b18881c420df31edc0863d9ced587981bd
ec9ac223ff814fc7230fbe6502bd0af1f6e01550dc2a548e02c7aa2403064c9c368dc
e1b920100000000000000000000000000000000000000000000000000000000000000
P1 binding_factor: d8ef5f6c4e28e13cb259855651e7f3e4720b8403ddd683eda0
1692d08a2c300e
P3 hiding_nonce_randomness: 7fe870d8a14f385e15df7766480d59b08000bcb98
0be46aa71d81986beea70ab
P3 binding_nonce_randomness: c00f0346984386e5028354dffc685346d38634c1
7edfc1115320ac4d12470ea3
P3 hiding_nonce: 14a7000070d7676f0d626a6e91e8744ed6e80a34cccc7e4a2372
0c9492329405
P3 binding_nonce: e019e71a8f4dce92fb967ac6fa0e3fcb8b857ab208aaceb113a
5f1c378d33500
P3 hiding_nonce_commitment: 54beede01c1eb25cf4f3e915c744c823ef1fe9547
f35d0cee101eef5f8aa2736
P3 binding_nonce_commitment: ea706f466f860c6a48170e577a77a6588f01af8e
75aa318adb33d665a76ea832
P3 binding_factor_input: 9c245d5fc2e451c5c5a617cc6f2a20629fb317d9b1c1
915ab4bfa319d4ebf922c54dd1a5b3b754550c72734ac9255db8107a2b01f361754d9
f13f428c2f6de9ed98771b7e34d27c1ecc1b18881c420df31edc0863d9ced587981bd
ec9ac223ff814fc7230fbe6502bd0af1f6e01550dc2a548e02c7aa2403064c9c368dc
e1b920300000000000000000000000000000000000000000000000000000000000000
P3 binding_factor: 963f8a687f39810d06a1834ce9973aab3cbfb0758a139dd160
e9ef924b3e3502

// Signer round two outputs
P1 sig_share: e16dbb7dc4ecdb51b42f8070000396cf1fa8d5024f4df769d2f24b2
efe853c01
P3 sig_share: 3f04963b32e06adfa800ca91252f29e51ed4a7fadff024bd5b0ceaa
556754e07

sig: 5a0fa81a8f827bcc1dcb5b5b81358c468001c459a4eaab92ed0fbd6698db5626
207251b9f6cc46315d304a022632bfb43e7c7dfd2e3e1c272eff35d454fb8a08
~~~

## FROST(P-256, SHA-256)

~~~
// Configuration information
MAX_PARTICIPANTS: 3
MIN_PARTICIPANTS: 2
NUM_PARTICIPANTS: 2

// Group input parameters
participant_list: 1,3
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

// Signer round one outputs
P1 hiding_nonce_randomness: ae2f5d230028ed4a3ef2a42b02d100e8d26862d8b
2b56f02507b2c4e6a554ce1
P1 binding_nonce_randomness: 83207341b0c0cf03efd0c0016e246db63ac959c4
06e51a72951c74bd5c35f7d7
P1 hiding_nonce: 94cabca38958b68d87f346f23649037fdc733c83f1facc1c3478
c6c5616017b0
P1 binding_nonce: 9dcd75c4844100a8733c6dd2b85c4dc146d85a605798f07473a
5fb753d1e19eb
P1 hiding_nonce_commitment: 03899f834845aa119c1a9063e893397a0e1cebe64
6555b9ccc86443d052008fa1f
P1 binding_nonce_commitment: 02b0ef95a36ff89822bdc19344e080f74f7313fe
46eeb05be2d85548fe0a7c3a8f
P1 binding_factor_input: 350c8b523feea9bb35720e9fbe0405ed48d78caa4fb6
0869f34367e144c68bb062b1cf9a77aaba3a463418ee9d1d6b1097f4f36aab944a6a1
fb2e4f58e44eb40000000000000000000000000000000000000000000000000000000
0000000001
P1 binding_factor: 71a2b67dca0629ee56613a62577ed4091590d80b2880f514eb
a28176d6565666
P3 hiding_nonce_randomness: 9575b12a642d508f2d197a2c1501f9fd9751166d4
9d9746896cd507382e4354a
P3 binding_nonce_randomness: 0925b65a16cfb21481c15e0b8af9520a411c4346
cc877a1d8d9352cb32beee58
P3 hiding_nonce: 16e04a8a6fbae9d02b6153143096aeada35e766582874efa0b58
ac8416d416ee
P3 binding_nonce: d7d30a0ccc0b470ccabd4b15e0edd09029c53be26f0e2abb66b
56e4185f6c35e
P3 hiding_nonce_commitment: 0283e67fc9bd55061ce8b04ae69852371779dffeb
7530a463bb6059176aa493dbd
P3 binding_nonce_commitment: 024203f31e6377076d1c8995623ed3be44cf4846
2612d714b248af58df3bce7d4e
P3 binding_factor_input: 350c8b523feea9bb35720e9fbe0405ed48d78caa4fb6
0869f34367e144c68bb062b1cf9a77aaba3a463418ee9d1d6b1097f4f36aab944a6a1
fb2e4f58e44eb40000000000000000000000000000000000000000000000000000000
0000000003
P3 binding_factor: 5434b6ffe1a10029fe1ac810b3f6f48cef0cccb8d200f18d42
8a04a056324a7b

// Signer round two outputs
P1 sig_share: 8fecfc0d5e104cc0fee07a4d6274014f3990c8369c8c72eee7f4711
a1fb0559c
P3 sig_share: f5c105909109506ecaf9a03322ec46202271ead1189ea5aade3dec0
31f78be94

sig: 039adcc0bdb63aa663f8015dbae9df3f61ebe5d5333ecb2532b24f1fc4b8d74f
d485ae019eef199d2ec9da1a808560476f9f1bb85a0e137a14d278925a42c5eedf
~~~

## FROST(secp256k1, SHA-256)

~~~
// Configuration information
MAX_PARTICIPANTS: 3
MIN_PARTICIPANTS: 2
NUM_PARTICIPANTS: 2

// Group input parameters
participant_list: 1,3
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

// Signer round one outputs
P1 hiding_nonce_randomness: a1a472bce75d6e2a20172e01a4207c8830e2b47c7
a36022b3c1f6401848cc3f9
P1 binding_nonce_randomness: c0143cb289298b1f6e1699723717de41f627d597
4d9c9dfdba27f0a5f95fc8fc
P1 hiding_nonce: e9db47128b59e5487f677ae6f562ac111b4c4e9b625b4173fee1
e318a9c16438
P1 binding_nonce: 3df6f03d333935d4ad24450ca70bae7755fe3f6eb5824f87e19
98410b4bf03fe
P1 hiding_nonce_commitment: 02e607b459d81a69cee96e8914f4161c145ce94c8
23f6e746e02abb81673ea03d8
P1 binding_nonce_commitment: 02d3c28d4a741556ebaf12fdc93757baf8361045
18de003ec15bd074941b1a3f0b
P1 binding_factor_input: a645d8249457bbcac34fa7b740f66bcce08fc39506b8
bbf1a1c81092f6272edad8d63e9ad230cf4d243bcacc1b9f967237c09a0e6fce70f1c
420bfdf35ee6e79000000000000000000000000000000000000000000000000000000
0000000001
P1 binding_factor: 8cb5510fc0822e6086aa9f734559ef2b0546e14407169d9526
bda65f8bfd7cfb
P3 hiding_nonce_randomness: 82766a142d21a4edd26a9ba219869339628874a15
00b228fdc506044d3792623
P3 binding_nonce_randomness: d280f87a7d13a681b61b8a65cc9a5ae85b41a1f1
a394d08838699505b8067855
P3 hiding_nonce: 4f675b1f95c30dc773f22aeb18baeab3bc71e32d16380d611f34
6d1ee2423294
P3 binding_nonce: b6f98388b0db4f7e0f9f6f400859099347e462be74d77980757
30b7edadff65f
P3 hiding_nonce_commitment: 025624fbe024c7f71203c10c3fe23949eaf562c34
9319ffca3504d0c4c26b4bf74
P3 binding_nonce_commitment: 03a205769ebbc1ae86a43a6ed997e9c88495941e
e28a9799cc0692c79cff777b4a
P3 binding_factor_input: a645d8249457bbcac34fa7b740f66bcce08fc39506b8
bbf1a1c81092f6272edad8d63e9ad230cf4d243bcacc1b9f967237c09a0e6fce70f1c
420bfdf35ee6e79000000000000000000000000000000000000000000000000000000
0000000003
P3 binding_factor: c358ecfba0a5246e47bfefa592ff67e196fd03f6c09443166e
67e4b0639aed60

// Signer round two outputs
P1 sig_share: 8712272abfc1304750c555257f5125a9a67a03ef473341b566ac775
75f0627c0
P3 sig_share: d55156e13694ba72d82da3b1240dcc8270e45f19038b4db7e98e1dd
34cf093a2

sig: 026036c3e187d1dce5c6f07c89fc0bcdce02e38d74120aba81a54662f5a104c9
a75c637e0bf655eaba28f2f8d6a35ef22d5caf86219b75ef319068369ddbc07a21
~~~
