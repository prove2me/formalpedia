-- Prove2me | solution 1 for AffineStats.exists_colouring_hitSet_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:40:47.874865+00:00
-- url     : https://prove2.me/submissions/384f29e1-9e03-4657-9cc6-6ffba2fefa8a

-- Sol generated from Applications/AffineSubspaceStats/RandomConstruction.lean
import Mathlib
import Definitions.Def_Applications_AffineSubspaceStats_AffineStats
import Definitions.Def_Applications_AffineSubspaceStats_RandomConstruction
import Theorems.Thm_AffineStats_card_Vec
import Theorems.Thm_AffineStats_card_exactly_one
import Theorems.Thm_AffineStats_cnt_colSet
import Theorems.Thm_AffineStats_pt_injective
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



lemma card_cubeSet {c : Vec n} {v : Fin d → Vec n} (hv : Indep v) :
    (cubeSet c v).card = 2 ^ d := by
  rw [cubeSet, Finset.card_image_of_injective _ (pt_injective c hv), Finset.card_univ]
  simp


/-- For a nondegenerate cube, the number of colourings for which the cube meets `g⁻¹(0)`
in exactly one point is `2^d · m^{2^d-1} · (m+1)^{2ⁿ-2^d}`. -/
lemma card_colourings_cnt_one (m : ℕ) (c : Vec n) {v : Fin d → Vec n} (hv : Indep v) :
    (univ.filter fun g : Vec n → Fin (m + 1) => cnt (colSet m g) c v = 1).card
      = 2 ^ d * (m ^ (2 ^ d - 1) * (m + 1) ^ (2 ^ n - 2 ^ d)) := by
  classical
  have hcong : (univ.filter fun g : Vec n → Fin (m + 1) => cnt (colSet m g) c v = 1)
      = (univ.filter fun g : Vec n → Fin (m + 1) =>
          ((cubeSet c v).filter fun x => g x = 0).card = 1) := by
    refine Finset.filter_congr (fun g _ => ?_)
    rw [cnt_colSet m g c hv]
  rw [hcong, card_exactly_one, card_cubeSet hv, card_Vec]
















open Filter





open AffineStats in
theorem solution(n d m : ℕ) :
    ∃ g : Vec n → Fin (m + 1),
      (univ.filter fun p : Param n (d + 1) => Indep p.2).card *
          (2 ^ (d + 1) * (m ^ (2 ^ (d + 1) - 1) * (m + 1) ^ (2 ^ n - 2 ^ (d + 1))))
        ≤ (m + 1) ^ (2 ^ n) * (hitSet n (d + 1) (colSet m g) 1).card := by
  classical
  set C := 2 ^ (d + 1) * (m ^ (2 ^ (d + 1) - 1) * (m + 1) ^ (2 ^ n - 2 ^ (d + 1))) with hC
  set IP := (univ.filter fun p : Param n (d + 1) => Indep p.2).card with hIP
  set K := (m + 1) ^ (2 ^ n) with hK
  have hKcard : Fintype.card (Vec n → Fin (m + 1)) = K := by
    rw [hK, Fintype.card_fun, card_Vec]
    simp
  by_contra hcon
  push_neg at hcon
  -- double counting
  have hdc : ∑ g : Vec n → Fin (m + 1), (hitSet n (d + 1) (colSet m g) 1).card
      = ∑ p : Param n (d + 1),
          (univ.filter fun g : Vec n → Fin (m + 1) => cnt (colSet m g) p.1 p.2 = 1).card := by
    simp only [hitSet, Finset.card_filter]
    exact Finset.sum_comm
  have hlow : IP * C ≤ ∑ p : Param n (d + 1),
      (univ.filter fun g : Vec n → Fin (m + 1) => cnt (colSet m g) p.1 p.2 = 1).card := by
    calc IP * C = ∑ _p ∈ univ.filter (fun p : Param n (d + 1) => Indep p.2), C := by
          rw [Finset.sum_const, smul_eq_mul, hIP]
      _ = ∑ p ∈ univ.filter (fun p : Param n (d + 1) => Indep p.2),
            (univ.filter fun g : Vec n → Fin (m + 1) => cnt (colSet m g) p.1 p.2 = 1).card := by
          refine Finset.sum_congr rfl (fun p hp => ?_)
          rw [hC, card_colourings_cnt_one m p.1 (Finset.mem_filter.mp hp).2]
      _ ≤ ∑ p : Param n (d + 1),
            (univ.filter fun g : Vec n → Fin (m + 1) => cnt (colSet m g) p.1 p.2 = 1).card :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hup : ∑ g : Vec n → Fin (m + 1), K * (hitSet n (d + 1) (colSet m g) 1).card
      < ∑ _g : Vec n → Fin (m + 1), IP * C :=
    Finset.sum_lt_sum_of_nonempty ⟨fun _ => 0, mem_univ _⟩ (fun g _ => hcon g)
  rw [Finset.sum_const, Finset.card_univ, hKcard, smul_eq_mul, ← Finset.mul_sum, hdc] at hup
  exact absurd (Nat.mul_le_mul_left K hlow) (not_le.mpr hup)
