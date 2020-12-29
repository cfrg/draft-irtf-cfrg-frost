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
 -
    ins: C. Komlo
    name: Chelsea Komlo
    organization: University of Waterloo, Zcash Foundation
    email: ckomlo@uwaterloo.ca

 -
    ins: I. Goldberg
    name: Ian Goldberg
    organization: University of Waterloo
    email: iang@uwaterloo.ca

informative:



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

Here, we define FROST only over prime-order groups over an elliptic curve such
as Ristretto or Decaf.

# Security Considerations

TODO Security


# IANA Considerations

This document has no IANA actions.



--- back

# Acknowledgments
{:numbered="false"}

TODO acknowledge.
