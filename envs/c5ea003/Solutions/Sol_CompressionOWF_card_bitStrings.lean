-- Prove2me | solution 1 for CompressionOWF.card_bitStrings
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T06:05:34.472517+00:00
-- url     : https://prove2.me/submissions/4dd30c2b-9a1e-4e2a-ae7b-e5d8c1ecf952

-- Sol generated from Speculative/AutoResearch/CompressionOneWayFunctions.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_CompressionOneWayFunctions
/-
Copyright (c) 2025. All rights reserved.

# Compression and One-Way Functions

## Overview

This file develops a fully formal, finitary account of the folklore link between
**compression** (finding short descriptions of strings) and **cryptographic
hardness** (inverting one-way functions).  It is the Phase-B/Milestone-M8
component of the research programme *Compression Beyond the Pigeonhole Bound*:
its purpose is to calibrate exactly how far randomness (and, more generally,
computational power) can push a compressor.

The development has four layers.

### 1. Description systems and the pigeonhole ceiling

A *decompressor* is any map `D : Str → α` from bit strings to objects.  The
complexity `K D y` is the length of a shortest `D`-program for `y`.  The
counting theorem `card_le_of_K_le` says: at most `2^(s+1) - 1` objects have
complexity `≤ s`.  This is the information-theoretic ceiling; no amount of
computational power moves it.

### 2. Randomness: the seed-budget theorem

`card_le_of_K_le_seeded` shows that a *seeded* (randomized) family of
decompressors indexed by a finite seed space `R` compresses at most
`|R| * (2^(s+1) - 1)` objects to `s` bits, i.e. randomness buys at most
`log₂|R| + 1` bits.  `seeded_prefix_covers` gives a matching construction
achieving exactly `log₂|R|` bits.  Together (`randomness_gain_exact`) they pin
down the worst-case value of randomness for compression: **exactly the seed
length, and no more**.

### 3. Compression search ⇋ inversion

`ShortestFinder D A` is the *compression-search task*: `A` must output a
shortest `D`-program for every describable `y` (the finitary analogue of
solving MINKT / computing `K^t` with a witness).  `Inverts f A` is the
*inversion task*.  The two are shown to be equivalent relative to any class of
algorithms closed under length guarding and bounded search:

* `shortestFinder_inverts` : compression search is at least as hard as inversion;
* `searchFinder_correct`   : inverters for the length-guarded functions
  `guardFun f l` can be combined, by a bounded linear search over the guard
  length, into a genuine shortest-program finder;
* `inversion_iff_shortest_compression` : the two tasks are equivalent for a
  `SearchClosedClass`;
* `owf_iff_compression_hard` : **one-way functions exist iff the
  compression-search problem is hard**.

### 4. Consequences for achievable worst-case bounds

`owf_description_gap` isolates the phenomenon that motivates the whole
programme: under a one-way function, there are strings whose short descriptions
*provably exist* (indeed have length bounded by an allowed resource bound) and
which *no efficient algorithm ever outputs*.  Combined with the pigeonhole
ceiling this gives the calibration statement `compression_calibration`.

All results are proved from scratch; there are no axioms and no `sorry`.
-/

open CompressionOWF


/-! ## Section 0: A concrete injective code for bit strings

We need the elementary fact that there are fewer than `2^(s+1)` bit strings of
length at most `s`.  Rather than importing a counting instance we build the
standard "leading one" numeral, which turns a bit string into a positive
natural number, injectively, with `natCode p < 2^(|p|+1)`. -/





/-! ## Section 1: Description systems and Kolmogorov-style complexity -/


variable {α : Type*}









/-! ## Section 2: The pigeonhole bound is attained, and randomness gains exactly
the seed length -/








/-! ## Section 3: Compression search and inversion -/









/-! ## Section 4: Classes of algorithms, one-way functions, and the equivalence -/








/-! ## Section 5: Consequences for achievable worst-case bounds -/






/-! ### A class in which a one-way function genuinely exists

The equivalence would be vacuous if the closure axioms of `SearchClosedClass`
forced every function to be invertible.  They do not: the class of
length-nondecreasing algorithms is closed under guarding and bounded search, and
the tagging function `p ↦ true :: p` is one-way for it (any inverter must delete
a bit, which the class forbids).  Consequently, by `owf_iff_compression_hard`,
the compression-search problem is hard for that class as well. -/






open CompressionOWF in
theorem solution(n : ℕ) : (bitStrings n).card = 2 ^ n := by
  rw [bitStrings, Finset.card_image_of_injective _ List.ofFn_injective]
  simp
