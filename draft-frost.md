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

# Notation

# Cryptographic Dependencies

## Elliptic Curve Operations

Here, we describe at a high level the operations that FROST requires for a
group instantiated over an elliptic curve. We describe in a later section how
these operations are implemented for specific curves.

### Generation of Group Elements

### Validation of Group Elements

### Group Operations

# Protocol Overview

# FROST Key Generation

## Trusted Dealer

## Distributed Key Generation

# FROST Signing

## Two Round

## Single Round



--- back

# Acknowledgments
{:numbered="false"}

TODO acknowledge.
