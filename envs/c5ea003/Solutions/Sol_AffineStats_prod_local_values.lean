-- Prove2me | solution 1 for AffineStats.prod_local_values
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:25:09.35058+00:00
-- url     : https://prove2.me/submissions/3b0ceac7-c6dc-4c2f-8945-844487706695

-- Sol generated from Applications/AffineSubspaceStats/RandomConstruction.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
import Definitions.Def_Applications_AffineSubspaceStats_RandomConstruction
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
theorem solution(T : Finset α) (m : ℕ) {x₀ : α} (hx₀ : x₀ ∈ T)
    (h : α → ℕ) (hh : ∀ x, h x = if x = x₀ then 1 else if x ∈ T then m else m + 1) :
    (∏ x : α, h x) = m ^ (T.card - 1) * (m + 1) ^ (Fintype.card α - T.card) := by
  classical
  rw [← Finset.prod_mul_prod_compl T h]
  congr 1
  · rw [← Finset.prod_erase_mul T h hx₀, hh x₀, if_pos rfl, mul_one]
    rw [Finset.prod_congr rfl (fun x hx => by
      rw [hh x, if_neg (Finset.mem_erase.mp hx).1, if_pos (Finset.mem_erase.mp hx).2])]
    rw [Finset.prod_const, Finset.card_erase_of_mem hx₀]
  · rw [Finset.prod_congr rfl (fun x hx => by
      have hxT : x ∉ T := Finset.mem_compl.mp hx
      rw [hh x, if_neg (by rintro rfl; exact hxT hx₀), if_neg hxT])]
    rw [Finset.prod_const, Finset.card_compl]
