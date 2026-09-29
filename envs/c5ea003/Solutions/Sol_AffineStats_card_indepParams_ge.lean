-- Prove2me | solution 1 for AffineStats.card_indepParams_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:34:00.91804+00:00
-- url     : https://prove2.me/submissions/cf080e63-e952-4d57-8f8c-d33857eb515e

-- Sol generated from Applications/AffineSubspaceStats/RandomConstruction.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
import Definitions.Def_Applications_AffineSubspaceStats_RandomConstruction
import Theorems.Thm_AffineStats_card_indepParams
import Theorems.Thm_AffineStats_card_indep_ge
/-
# Affine subspace statistics in `𝔽₂ⁿ`: the random construction for `s = 1`

This file continues the development of
`Catalog/Applications/AffineSubspaceStats/AffineStats.lean`, where the model
(random affine `d`-cubes in `𝔽₂ⁿ`, the statistic `cnt`, the probability `flatProb`)
is set up.

The paper's `s = 1` regime is governed by a *random* construction: keep each point of
`𝔽₂ⁿ` independently with probability `p`.  A `d`-flat `F` has `2^d` points, so it meets
such a random set in exactly one point with probability `2^d · p · (1-p)^{2^d - 1}`,
which is maximised at `p = 2^{-d}`, giving `(1 - 2^{-d})^{2^d - 1} → e^{-1}`.

We formalise this as a *counting* argument (no measure theory): instead of a random
subset we average over the `(m+1)^{2ⁿ}` colourings `g : 𝔽₂ⁿ → Fin (m+1)` and take
`A = g⁻¹(0)`, which realises `p = 1/(m+1)` exactly.  The combinatorial heart is
`AffineStats.card_exactly_one`: for a fixed set `T` of `t` points, exactly
`t · m^{t-1} · (m+1)^{|α| - t}` colourings vanish at exactly one point of `T`.

The main results are

* `AffineStats.exists_flatProb_one_ge` :
  `∃ A, λ(d+1,1) ≥ (2^{d+1}·m^{2^{d+1}-1} / (m+1)^{2^{d+1}}) · (1 - (2^{d+1}-1)/2ⁿ)`
  for every `m`;
* `AffineStats.exists_flatProb_one_ge_opt` : the choice `m + 1 = 2^{d+1}`, giving
  `λ(d+1,1) ≥ (1 - 2^{-(d+1)})^{2^{d+1}-1} · (1 - (2^{d+1}-1)/2ⁿ)`;
* `AffineStats.maxFlatProb_one_ge_limit` : hence
  `λ*(d+1,1) ≥ (1 - 2^{-(d+1)})^{2^{d+1}-1}`, which for `d = 0` is the exact value `1/2`
  and for every `d` beats the algebraic construction of
  `Catalog/Applications/AffineSubspaceStats/ExactProduct.lean` (e.g. `27/64` versus
  `3/8` for `2`-flats).
-/

open AffineStats

open Finset


variable {α : Type*} [Fintype α] [DecidableEq α]






variable {n d : ℕ}





















open Filter





open AffineStats in
theorem solution(n d : ℕ) :
    2 ^ (n * (d + 1 + 1)) ≤ (univ.filter fun p : Param n (d + 1) => Indep p.2).card
      + (2 ^ (d + 1) - 1) * 2 ^ (n * (d + 1)) := by
  have h1 := card_indep_ge n d
  have h2 := card_indepParams n d
  have h4 : 2 ^ n * 2 ^ (n * (d + 1)) = 2 ^ (n * (d + 1 + 1)) := by
    rw [← pow_add]; congr 1; ring
  have h5 : 2 ^ n * ((2 ^ (d + 1) - 1) * 2 ^ (n * d))
      = (2 ^ (d + 1) - 1) * 2 ^ (n * (d + 1)) := by
    rw [show (2 : ℕ) ^ (n * (d + 1)) = 2 ^ (n * d) * 2 ^ n from by
      rw [← pow_add, Nat.mul_succ]]
    ring
  calc 2 ^ (n * (d + 1 + 1)) = 2 ^ n * 2 ^ (n * (d + 1)) := h4.symm
    _ ≤ 2 ^ n * ((univ.filter fun v : Fin (d + 1) → Vec n => Indep v).card
          + (2 ^ (d + 1) - 1) * 2 ^ (n * d)) := Nat.mul_le_mul_left _ h1
    _ = 2 ^ n * (univ.filter fun v : Fin (d + 1) → Vec n => Indep v).card
          + 2 ^ n * ((2 ^ (d + 1) - 1) * 2 ^ (n * d)) := by ring
    _ = (univ.filter fun p : Param n (d + 1) => Indep p.2).card
          + (2 ^ (d + 1) - 1) * 2 ^ (n * (d + 1)) := by rw [h5, h2]
