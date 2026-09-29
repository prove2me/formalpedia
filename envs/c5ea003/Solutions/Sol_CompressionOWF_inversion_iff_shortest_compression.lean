-- Prove2me | solution 1 for CompressionOWF.inversion_iff_shortest_compression
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T06:14:38.009739+00:00
-- url     : https://prove2.me/submissions/46dbd391-160d-40a4-af34-7686cd03983e

-- Sol generated from Speculative/AutoResearch/CompressionOneWayFunctions.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_CompressionOneWayFunctions
import Theorems.Thm_CompressionOWF_K_le_of_eq
import Theorems.Thm_CompressionOWF_searchFinder_correct
import Theorems.Thm_CompressionOWF_shortestFinder_inverts
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



/-- Guarded functions inherit honesty, with bound `max l n`. -/
lemma honest_guardFun (C : SearchClosedClass) (f : Str → Str) (l : ℕ) :
    HonestIn C (guardFun f l) := by
  refine ⟨fun n => max l n, C.allowed_max _ _ (C.allowed_const l) C.allowed_id, ?_⟩
  rintro y ⟨p, hp⟩
  show K (guardFun f l) y ≤ max l y.length
  have h1 : K (guardFun f l) y ≤ p.length := K_le_of_eq hp
  by_cases hlen : p.length ≤ l
  · exact le_trans h1 (le_trans hlen (le_max_left _ _))
  · have h2 : y.length = p.length + 1 := by
      rw [← hp]; simp [guardFun, if_neg hlen]
    exact le_trans h1 (le_trans (by omega : p.length ≤ y.length) (le_max_right l y.length))





/-! ## Section 5: Consequences for achievable worst-case bounds -/






/-! ### A class in which a one-way function genuinely exists

The equivalence would be vacuous if the closure axioms of `SearchClosedClass`
forced every function to be invertible.  They do not: the class of
length-nondecreasing algorithms is closed under guarding and bounded search, and
the tagging function `p ↦ true :: p` is one-way for it (any inverter must delete
a bit, which the class forbids).  Consequently, by `owf_iff_compression_hard`,
the compression-search problem is hard for that class as well. -/






open CompressionOWF in
theorem solution(C : SearchClosedClass) :
    (∀ f ∈ C.Comp, HonestIn C f → ∃ A ∈ C.Comp, Inverts f A) ↔
    (∀ f ∈ C.Comp, HonestIn C f → ∃ A ∈ C.Comp, ShortestFinder f A) := by
  constructor
  · intro hinv f hf hhon
    obtain ⟨b, hb, hbound⟩ := hhon
    have hstep : ∀ l : ℕ, ∃ A : Str → Str, A ∈ C.Comp ∧ Inverts (guardFun f l) A := by
      intro l
      obtain ⟨A, hA1, hA2⟩ :=
        hinv (guardFun f l) (C.guard_mem f hf l) (honest_guardFun C f l)
      exact ⟨A, hA1, hA2⟩
    choose A hAmem hAinv using hstep
    refine ⟨searchFinder f A b, C.search_mem f hf A hAmem b hb, ?_⟩
    intro y hy
    exact searchFinder_correct f A b hAinv y hy (hbound y hy)
  · intro hcomp f hf hhon
    obtain ⟨A, hA1, hA2⟩ := hcomp f hf hhon
    exact ⟨A, hA1, shortestFinder_inverts hA2⟩
