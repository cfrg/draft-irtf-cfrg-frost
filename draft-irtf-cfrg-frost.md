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
This variant of FROST specifically defines key generation with a trusted dealer and
two-round signing operations.
Finally, this draft specifies signatures that are compatible with EdDSA verification of
signatures, bui not EdDSA nonce generation.


--- middle

# Introduction

DISCLAIMER: This is a work-in-progress draft of FROST.

RFC EDITOR: PLEASE REMOVE THE FOLLOWING PARAGRAPH The source for this draft is
maintained in GitHub. Suggested changes should be submitted as pull requests
at https://github.com/chelseakomlo/frost-spec. Instructions are on that page as
well.

In this draft, we present a variant of FROST, a Flexible Round-Optimized Schnorr Threshold
signature scheme.
FROST achieves its efficiency improvements in part by allowing the signing
protocol to abort in the presence of a misbehaving participant (who can be
identified and excluded from future signing operations).
FROST remains EUF-CMA (existential unforgeability against chosen message attacks) secure
assuming an adversary can corrupt no more than `(t-1)` participants.

Here, we specify the variant of FROST that requires a trusted dealer to perform
key generation. Further, this draft specifies only two-round signing operations.
This draft specifies signatures that are compatible with EdDSA verification of
signatures, bui not EdDSA nonce generation. EdDSA-style nonce-generation, where the
nonce is derived deterministically, is insecure in a multi-party signature setting.

# Change Log

draft-01

- Submitted a full draft and added additional authors.

draft-00

- Submitted a basic draft after adoption of draft-komlo-frost as a working
  group item.

# Terminology

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT",
"SHOULD", "SHOULD NOT", "RECOMMENDED", "NOT RECOMMENDED", "MAY", and
"OPTIONAL" in this document are to be interpreted as described in
BCP 14 {{!RFC2119}} {{!RFC8174}} when, and only when, they appear in all
capitals, as shown here.

# Basic Assumptions

We maintain the following assumptions.

* Selection of participants. We assume implementations determine how participants
are selected for key generation and signing.
* Handling failures. We do not specify how implementations should handle failures.
* Sampling of secrets. We assume that secrets are sampled uniformly at random.

# Security Considerations

* Trusted dealer. The dealer that performs key generation is trusted to follow
the protocol, although participants still are able to verify the consistency of their
shares via a VSS (verifiable secret sharing) step.

* Unforgeability assuming less than `(t-1)` corrupted signers. So long as an adverary
corrupts fewer than `t-1` participants, the scheme remains secure against EUF-CMA attacks.

## Communication channels

* Key Generation. At the time of key generation, we assume an authenticated, confidential, and
reliable channel. Specifically, the dealer must be able to transmit secret key material to each
participant over this channel.
* Signing. At the time of signing, we assume a reliable channel. While messages that are exchanged
contain no secret information, the channel must be able to deliver messages reliably in order for
the protocol to complete.

## Protocol Failures

In the case of failures (such as when a verification check returns invalid), participants must
abort the protocol. We do not specify what implementations should
do in the case of failure after aborting.

# Notation

The following notation and terminology are used throughout this document.

* `s` denotes a secret.
* `s_i` denotes the ith share of the secret `s`.
* A participant is an entity that is trusted to hold a secret share.
* `n` denotes the number of participants, and the number of shares that `s` is split into.
* `t` denotes the threshold number of participants required to issue a signature. More specifically,
at least `t` shares must be combined to issue a valid signature.
* `C` represents the coalition of signers, and is a set of participant identifiers of size at least `t`.
* `l_i` represents the ith Lagrange coefficient.
* `sig = (R, z)` denotes a signature with public commitment `R` and response `z`.
* `PK` is the group public key.
* `sk_i` is each ith individual's private key.


# Cryptographic Dependencies

FROST variants rely on the following primitives.

* Group operations over an elliptic curve group.

  - Deirdre will write this section.

* EdDSA Verification

  - `"Verify(PK, sig)"` outputs accept or fail

# Protocol Overview

Chelsea will write this

# Two-Round FROST with Trusted Dealer

## Trusted Dealer Key Generation

Chelsea will write this

## Signing

Chelsea will write this

# Curve and Verification Compatability

Deirdre will write this.

* EdDSA over edwards25519 (RFC 8032)

* EdDSA over Ristretto

# Serialization and Message Format

Teor will write this.

# Security Considerations

##  External Requirements / Non-Goals

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
