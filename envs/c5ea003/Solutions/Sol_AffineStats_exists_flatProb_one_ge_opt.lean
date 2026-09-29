-- Prove2me | solution 1 for AffineStats.exists_flatProb_one_ge_opt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:44:53.48437+00:00
-- url     : https://prove2.me/submissions/98c7eef5-cae9-4646-9729-fd6bb76845c0

-- Sol generated from Applications/AffineSubspaceStats/RandomConstruction.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
import Definitions.Def_Applications_AffineSubspaceStats_RandomConstruction
import Theorems.Thm_AffineStats_exists_flatProb_one_ge
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












/-- A convenient algebraic identity: `((a-1)/a)^t = a(a-1)^t / a^{t+1}`. -/
lemma div_pow_shift (a : ℚ) (t : ℕ) (ha : a ≠ 0) :
    ((a - 1) / a) ^ t = a * (a - 1) ^ t / a ^ (t + 1) := by
  rw [div_pow, pow_succ]
  field_simp









open Filter





open AffineStats in
theorem solution(n d : ℕ) (hdn : d + 1 ≤ n) :
    ∃ A : Finset (Vec n),
      (((2 : ℚ) ^ (d + 1) - 1) / 2 ^ (d + 1)) ^ (2 ^ (d + 1) - 1)
          * (1 - (2 ^ (d + 1) - 1) / 2 ^ n) ≤ flatProb n (d + 1) A 1 := by
  obtain ⟨A, hA⟩ := exists_flatProb_one_ge n d (2 ^ (d + 1) - 1) hdn
  refine ⟨A, le_trans (le_of_eq ?_) hA⟩
  congr 1
  have hc : ((2 ^ (d + 1) - 1 : ℕ) : ℚ) = (2 : ℚ) ^ (d + 1) - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
  rw [hc, show ((2 : ℚ) ^ (d + 1) - 1) + 1 = (2 : ℚ) ^ (d + 1) from by ring]
  set t := 2 ^ (d + 1) - 1 with ht
  have h1 : (1 : ℕ) ≤ 2 ^ (d + 1) := Nat.one_le_two_pow
  have hpow : (2 : ℕ) ^ (d + 1) = t + 1 := by omega
  rw [hpow]
  exact div_pow_shift _ t (by positivity)
