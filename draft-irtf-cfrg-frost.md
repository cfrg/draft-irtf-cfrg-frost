---
title: "FROST: Flexible Round-Optimized Schnorr Threshold Signatures"
abbrev: "FROST"
docname: draft-komlo-frost
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

informative:
  frost:
    target: https://eprint.iacr.org/2020/852.pdf
    title: "FROST: Flexible Round-Optimized Schnorr Threshold Signatures"
    author:
      - name: Chelsea Komlo
      - name: Ian Goldberg
    date: 2020-07-08



--- abstract

In this draft, we present FROST, a Flexible Round-Optimized Schnorr Threshold
signature scheme that reduces network overhead during signing operations while
protecting against forgery attacks applicable to prior similar threshold and
multisignature constructions.

FROST can be safely used without limiting concurrency of signing operations yet
allows for true threshold signing, as only a threshold number of participants
are required for signing operations. Here, we define FROST as a two-round
protocol, but it can be optimized to a single-round single-round signing protocol
as the first round can be performed as a batched pre-processing stage.

--- middle

# Introduction

DISCLAIMER: This is a work-in-progress draft of FROST.

RFC EDITOR: PLEASE REMOVE THE FOLLOWING PARAGRAPH The source for this draft is
maintained in GitHub. Suggested changes should be submitted as pull requests
at https://github.com/chelseakomlo/frost-spec. Instructions are on that page as
well.

In this draft, we present FROST, a Flexible Round-Optimized Schnorr Threshold
signature scheme. FROST reduces network overhead during signing operations by
optimizing for efficiency over robustness. FROST uses a novel technique to
allow for fully parallelized use while protecting against forgery attacks that
are applicable to prior similar threshold and multisignature constructions.

FROST achieves its efficiency improvements in part by allowing the signing
protocol to abort in the presence of a misbehaving participant (who can be
identified and excluded from future signing operations).

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

We maintain assumptions about how participants are selected as well as
responsibilities of the underlying network channel. Further, we do not specify
how implementations should handle failures that occur during the execution of
FROST key generation or signing operations.

## Selection of participants

We assume that at the time of key generation, participants have a mechanism to
select other participants.

## Communication channels

We assume that participants communicate
over an authenticated and trustworthy channel. Note that during signing,
participants can communicate over any channel. We assume that communication
failures (dropped messages, etc) are handled externally to the protocol.

## Protocol Failures

FROST is not robust; in the case of failures, participants must
abort the protocol and try again. However, failures may occur due to
participant misbehavior. As such, we do not specify what implementations should
do in the case of failure after aborting the protocol.

# Notation

To be completed

# Cryptographic Dependencies

To be completed

# Protocol Overview

To be completed

# FROST Key Generation

To be completed

# FROST Signing

To be completed




--- back

# Acknowledgments
{:numbered="false"}

TODO acknowledge.
