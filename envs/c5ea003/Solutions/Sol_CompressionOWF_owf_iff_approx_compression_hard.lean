-- Prove2me | solution 1 for CompressionOWF.owf_iff_approx_compression_hard
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T06:16:00.904178+00:00
-- url     : https://prove2.me/submissions/a045a7fc-0031-4ba3-b722-3cbdf4c7817a

-- Sol generated from Speculative/AutoResearch/CompressionUniversality.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_CompressionOneWayFunctions
import Definitions.Def_Speculative_AutoResearch_CompressionUniversality
import Theorems.Thm_CompressionOWF_approxFinder_inverts
import Theorems.Thm_CompressionOWF_inversion_iff_shortest_compression
/-
Copyright (c) 2025. All rights reserved.

# Universal Description Systems, Derandomization, and Robustness of the
# Compression ⇋ One-Way-Function Equivalence

## Overview

This file is the second cycle of the Phase-B/M8 investigation begun in
`Shared.CompressionOneWayFunctions`.  There we proved

* the pigeonhole ceiling and its seeded (randomized) refinement, and
* the equivalence "inverting one-way functions ⇔ solving the
  compression-search (shortest-program) problem".

Here we build the missing structural layer and push the calibration further.

### 1. Self-delimiting codes and universality

`unaryTag`/`parseUnary` and `sdPair`/`parseSD` are prefix-free encodings with
verified parsing lemmas.  They yield:

* `K_univSys_le` — the **invariance theorem** in finitary form: a single
  universal decompressor simulates a whole family at an additive cost equal to
  the length of the index;
* `K_pairSys_le` — **subadditivity**: describing `x ++ y` costs at most
  `2·K x + 1 + K y`.

### 2. Derandomization: buying back randomness at the seed price

`derandomization_cost` shows that a seeded family of decompressors is simulated
by *one* deterministic decompressor at additive cost `2k + 1` for `k`-bit seeds.
Combined with `card_le_of_K_le_seeded` (which says randomness can never buy more
than `log₂|R| + 1` bits) this closes the loop: **the value of randomness for
compression is its seed length, and it is always purchasable deterministically
at that same price, up to a factor two.**

### 3. Most strings are incompressible

`density_incompressible`: for every decompressor, at most a `2^{-(c-1)}`
fraction of the strings of length `n` have complexity `≤ n - c`.

### 4. Robustness of the cryptographic equivalence

`inversion_iff_approx_compression`: the equivalence with inversion survives an
*arbitrary additive slack* `δ` in the compression task.  Finding descriptions
that are merely within `δ(n)` bits of optimal is still exactly as hard as
inverting one-way functions.  Consequently `owf_gap_universal` shows that
switching to a universal description system does not close the gap between
*existing* and *findable* descriptions.

No axioms beyond the standard three, and no `sorry`.
-/

open CompressionOWF

/-! ## Section 1: Self-delimiting codes -/









/-! ## Section 2: Universal decompressors and the invariance theorem -/





/-! ## Section 3: Subadditivity of complexity -/



/-! ## Section 4: Derandomization at the seed price -/




/-! ## Section 5: Most strings are incompressible -/


/-! ## Section 6: Robustness of the cryptographic equivalence -/



theorem shortestFinder_isApprox {D A : Str → Str} (δ : ℕ → ℕ)
    (h : ShortestFinder D A) : ApproxShortestFinder D A δ := by
  intro y hy
  obtain ⟨h1, h2⟩ := h y hy
  exact ⟨h1, by omega⟩

/-- **Robustness of the equivalence.**  For *any* additive slack `δ`, solving the
approximate compression-search problem for all honest decompressors of a class
is equivalent to inverting all honest functions of that class.  Approximation
does not make short-program finding easier than breaking one-way functions. -/
theorem inversion_iff_approx_compression (C : SearchClosedClass) (δ : ℕ → ℕ) :
    (∀ f ∈ C.Comp, HonestIn C f → ∃ A ∈ C.Comp, Inverts f A) ↔
    (∀ f ∈ C.Comp, HonestIn C f → ∃ A ∈ C.Comp, ApproxShortestFinder f A δ) := by
  constructor
  · intro hinv f hf hhon
    obtain ⟨A, hA1, hA2⟩ := (inversion_iff_shortest_compression C).1 hinv f hf hhon
    exact ⟨A, hA1, shortestFinder_isApprox δ hA2⟩
  · intro happ f hf hhon
    obtain ⟨A, hA1, hA2⟩ := happ f hf hhon
    exact ⟨A, hA1, approxFinder_inverts hA2⟩




open CompressionOWF in
theorem solution(C : SearchClosedClass) (δ : ℕ → ℕ) :
    (∃ f, OneWayIn C f) ↔
    (∃ D, D ∈ C.Comp ∧ HonestIn C D ∧ ∀ A ∈ C.Comp, ¬ ApproxShortestFinder D A δ) := by
  constructor
  · rintro ⟨f, hf, hhon, hhard⟩
    exact ⟨f, hf, hhon, fun A hA hS => hhard A hA (approxFinder_inverts hS)⟩
  · rintro ⟨D, hD, hhon, hhard⟩
    by_contra hcon
    push_neg at hcon
    have hinv : ∀ f ∈ C.Comp, HonestIn C f → ∃ A ∈ C.Comp, Inverts f A := by
      intro f hf hh
      have hnot := hcon f
      rw [OneWayIn] at hnot
      simp only [hf, hh, true_and, not_forall] at hnot
      obtain ⟨A, hA⟩ := hnot
      simp only [not_not] at hA
      exact ⟨A, hA.1, hA.2⟩
    obtain ⟨A, hA1, hA2⟩ :=
      (inversion_iff_approx_compression C δ).1 hinv D hD hhon
    exact hhard A hA1 hA2
