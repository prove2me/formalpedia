-- Prove2me | solution 1 for CompressionOWF.searchFinder_correct
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T06:13:12.508229+00:00
-- url     : https://prove2.me/submissions/a8b92617-b3bf-4389-87c9-ea596e8ab2ca

-- Sol generated from Speculative/AutoResearch/CompressionOneWayFunctions.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_CompressionOneWayFunctions
import Theorems.Thm_CompressionOWF_K_le_of_eq
import Theorems.Thm_CompressionOWF_exists_shortest
import Theorems.Thm_CompressionOWF_leastFrom_spec
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
theorem solution(f : Str → Str) (A : ℕ → Str → Str) (fuel : ℕ → ℕ)
    (hA : ∀ l, Inverts (guardFun f l) (A l)) (y : Str) (hy : Describable f y)
    (hfuel : K f y ≤ fuel y.length) :
    f (searchFinder f A fuel y) = y ∧ (searchFinder f A fuel y).length = K f y := by
  have hsf : searchFinder f A fuel y =
      A (leastFrom (fun l => decide (guardFun f l (A l (true :: y)) = true :: y))
        (fuel y.length)) (true :: y) := rfl
  rw [hsf]
  set P : ℕ → Bool := fun l => decide (guardFun f l (A l (true :: y)) = true :: y) with hP
  have hkey : ∀ l, P l = true ↔ K f y ≤ l := by
    intro l
    constructor
    · intro hl
      have h : guardFun f l (A l (true :: y)) = true :: y := by simpa [hP] using hl
      set q := A l (true :: y) with hq
      by_cases hlen : q.length ≤ l
      · have hfq : f q = y := by
          simp only [guardFun, if_pos hlen] at h
          simpa using h
        exact le_trans (K_le_of_eq hfq) hlen
      · simp only [guardFun, if_neg hlen] at h
        exact absurd h (by simp)
    · intro hl
      obtain ⟨p, hplen, hpf⟩ := exists_shortest hy
      have hdesc : Describable (guardFun f l) (true :: y) := by
        refine ⟨p, ?_⟩
        have hp : p.length ≤ l := by omega
        simp [guardFun, hp, hpf]
      have := hA l (true :: y) hdesc
      simpa [hP] using this
  have hex : ∃ l ≤ fuel y.length, P l = true := ⟨K f y, hfuel, (hkey _).2 le_rfl⟩
  obtain ⟨hgot, hmin⟩ := leastFrom_spec P (fuel y.length) hex
  set l0 := leastFrom P (fuel y.length) with hl0
  have hKle : K f y ≤ l0 := (hkey l0).1 hgot
  have hl0le : l0 ≤ K f y := by
    by_contra hcon
    push_neg at hcon
    have hfalse := hmin (K f y) hcon
    rw [(hkey (K f y)).2 le_rfl] at hfalse
    exact absurd hfalse (by simp)
  have hl0eq : l0 = K f y := le_antisymm hl0le hKle
  have h : guardFun f l0 (A l0 (true :: y)) = true :: y := by simpa [hP] using hgot
  set q := A l0 (true :: y) with hq
  by_cases hlen : q.length ≤ l0
  · have hfq : f q = y := by
      simp only [guardFun, if_pos hlen] at h
      simpa using h
    refine ⟨hfq, ?_⟩
    have h1 : K f y ≤ q.length := K_le_of_eq hfq
    have h2 : q.length ≤ K f y := hl0eq ▸ hlen
    omega
  · simp only [guardFun, if_neg hlen] at h
    exact absurd h (by simp)
