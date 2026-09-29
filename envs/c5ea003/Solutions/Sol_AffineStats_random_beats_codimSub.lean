-- Prove2me | solution 1 for AffineStats.random_beats_codimSub
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:58:14.291285+00:00
-- url     : https://prove2.me/submissions/038b6a9e-9090-4622-ae00-b595502513bf

-- Sol generated from Applications/AffineSubspaceStats/RandomConstruction.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
import Definitions.Def_Applications_AffineSubspaceStats_CodimSubspace
import Definitions.Def_Applications_AffineSubspaceStats_RandomConstruction
import Theorems.Thm_AffineStats_exists_flatProb_one_ge_opt
import Theorems.Thm_AffineStats_flatProb_one_eq_prod
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
theorem solution(n : ℕ) (hn : 5 ≤ n) :
    ∃ A : Finset (Vec n),
      flatProb n 2 (codimSub (m := 2) n (by omega)) 1 < flatProb n 2 A 1 := by
  obtain ⟨A, hA⟩ := exists_flatProb_one_ge_opt n 1 (by omega)
  refine ⟨A, lt_of_lt_of_le ?_ hA⟩
  rw [flatProb_one_eq_prod (d := 2) (n := n) (by omega)]
  have hprod : (∏ i : Fin 2, (1 - (2 : ℚ) ^ (i : ℕ) / 2 ^ 2)) = 3 / 8 := by
    rw [Fin.prod_univ_two]
    norm_num
  rw [hprod]
  have hpow : (2 : ℚ) ^ 5 ≤ 2 ^ n := by
    exact pow_le_pow_right₀ (by norm_num) hn
  have hpos : (0 : ℚ) < 2 ^ n := by positivity
  have herr : ((2 : ℚ) ^ (1 + 1) - 1) / 2 ^ n ≤ 3 / 32 := by
    rw [div_le_div_iff₀ hpos (by norm_num : (0:ℚ) < 32)]
    norm_num at hpow ⊢
    linarith
  have hval : (((2 : ℚ) ^ (1 + 1) - 1) / 2 ^ (1 + 1)) ^ (2 ^ (1 + 1) - 1) = 27 / 64 := by
    norm_num
  rw [hval]
  nlinarith [herr]
