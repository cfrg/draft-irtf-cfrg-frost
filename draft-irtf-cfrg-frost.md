---
title: "FROST: Flexible Round-Optimized Schnorr Threshold Signatures"
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

Let B be a generator, or distiguished element, of G, a finite group of with
order l, a large prime.  Throughout this document, and in practice, we assume
this group to be instantiated as an arbitrary abstraction of an elliptic curve
subgroup, defined over a finite field; however, that does not restrict an
implementation from instantiating FROST signatures over other groups, provided
their order be prime.

We denote group elements with capital Roman letters, and scalars with
lower-cased Roman letters.  We use + to denote the group operation, and - to
denote inversion.  We use * to denote multiplication of a scalar by a group
element, that is, the group element added to itself in succession a number of
times equal to the value of the scalar.  Let SUM(START, END){TERMS} denote the
summation from START to END (inclusive) of TERMS, e.g. SUM(N=0, 3){2N} is equal
to 2*(1+2+3)=12.  Let PROD(START, END){TERMS} denote the product from START to
END of TERMS in similar manner.  Testing equality between two group elements
is denoted as ?=, where it is assumed that the elements are in some canonical,
serialised form.

# Cryptographic Dependencies

To be completed

## Cryptographic Hash Function

We require the use of a cryptographically secure hash function, generically
written here as H, which functions effectively as a random oracle.  For
concrete recommendations on hash functions which SHOULD BE used in practice, see
[Appendix A: Recommended Ciphersuites].

XXXisis How do I link between sections with this setup?

## Pedersen Commitment

A Pedersen commitment is simply a commitment, C, to a uniquely valid opening, o,
by calculating C = o * B.

## Individual Keypair

An individual keypair is calculated as a scalar sampled in a uniformly
distributed manner, a, as the secret, and its public counterpart as A = a * B.

## Schnorr Signature

A Schnorr signature, (s, R), created with the secret-public keypair (a, A), over
the message m, is calculated as: r is a uniformly random scalar, calculated in
some manner such that if only one signing party remains honest that the
uniformly random requirement still holds.  R is then calculated as R = r * B.  k
is calculated as k = H(CIPHERSUITE || R || A || m), where CIPHERSUITE is a string
describing the specific instantiation properties of this FROST signature scheme,
e.g. "FROST-RISTRETTO255-SHA512" or "FROST-JUBJUB-BLAKE2B", see Appendix A for
more concrete details.  Finally, s is calculated as s = k * a + r, and the final
signature is constituted by the tuple (s, R).

To verify the signature, k is recalculated as before, R' is calculated as
R' = k * A + s * B, and then check R' ?= R.  If equal, return true; otherwise,
return false.

# Protocol Overview

The agreed upon participants in a t-out-of-n threshold signing instantiation
undertake a distributed key generation protocol to create individual keypairs,
as well as a shared group key.  Using the secret component of their individual
keypair, a participant MAY submit a partial signature on a given message.  These
partial signatures SHOULD be aggregated by an untrusted signature aggregator,
SA, who MAY be one of the individual signers.  The aggregated signature MUST be
a sigma protocol proof that at least t-out-of-n of the agreed upon participants
signed the given message.

# FROST Key Generation

To be completed

# FROST Signing

To be completed

# Appendices

## Appendix A: Recommended Ciphersuites

To be completed

--- back

# Acknowledgments
{:numbered="false"}

TODO acknowledge.
