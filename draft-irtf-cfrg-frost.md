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
 -  ins: R.L. Barnes
    name: Richard Barnes
    organization: Cisco
    email: rlb@ipv.sx

informative:
  frost:
    target: https://eprint.iacr.org/2020/852.pdf
    title: "Two-Round FROST with Trusted Dealer"
    author:
      - name: Chelsea Komlo
      - name: Ian Goldberg
      - name: Deirdre Connelly
      - name: Richard Barnes
    date: 2021-06-01



--- abstract

In this draft, we present a variant of FROST, a Flexible Round-Optimized Schnorr Threshold
signature scheme. FROST signatures can be issued after a threshold number of entities
cooperate to issue the trusted dealer, allowing for improved distribution of trust and
redundancy.

This variant specifically defines key generation with a trusted dealer and
two-round signing operations.

--- middle

# Introduction

DISCLAIMER: This is a work-in-progress draft of FROST.

RFC EDITOR: PLEASE REMOVE THE FOLLOWING PARAGRAPH The source for this draft is
maintained in GitHub. Suggested changes should be submitted as pull requests
at https://github.com/chelseakomlo/frost-spec. Instructions are on that page as
well.

In this draft, we present a variant of FROST, a Flexible Round-Optimized Schnorr Threshold
signature scheme. FROST reduces network overhead during signing operations by
optimizing for efficiency over robustness, while allowing secure
fully parallelized use.

FROST achieves its efficiency improvements in part by allowing the signing
protocol to abort in the presence of a misbehaving participant (who can be
identified and excluded from future signing operations).

Here, we specify the variant of FROST that requires a trusted dealer to perform
key generation, as well as signing operations that are performed in two rounds.

# Change Log

draft-00

- Submitted a basic draft after adoption of draft-komlo-frost as a working
  group item.

# Terminology

The key words "MUST", "MUST NOT", "REQUIRED", "SHALL", "SHALL NOT",
"SHOULD", "SHOULD NOT", "RECOMMENDED", "NOT RECOMMENDED", "MAY", and
"OPTIONAL" in this document are to be interpreted as described in
BCP 14 {{!RFC2119}} {{!RFC8174}} when, and only when, they appear in all
capitals, as shown here.

# Security Considerations

In this draft, we specify key generation using a trusted dealer.

# Basic Assumptions

We maintain the following assumptions.

* Selection of participants. We assume implementations determine how participants
are selected for for key generation and signing.
* Handling failures. We do not specify how implementations should handle failures.
* Sampling of secrets. We assume that secrets are sampled uniformly at random.
* The dealer that performs key generation is trusted.

## Communication channels

At the time of key generation, we assume an authenticated, confidential, and
reliable channel.
At the time of signing, we assume a reliable channel.

## Protocol Failures

In the case of failures, participants must abort the protocol.
We do not specify what implementations should
do in the case of failure after aborting the protocol. As such,
some implementations may wish to re-try immediately, whereas
others may wish to investigate the failure.

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


# Cryptographic Dependencies

FROST variants rely on the following primitives.


# Protocol Overview

To be completed

# FROST Key Generation

To be completed

# FROST Signing

To be completed


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
