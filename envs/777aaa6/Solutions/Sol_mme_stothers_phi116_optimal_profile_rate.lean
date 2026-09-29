-- Prove2me | solution 1 for mme_stothers_phi116_optimal_profile_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T08:20:06.755315+00:00
-- url     : https://prove2.me/submissions/df9b87de-b462-486f-ad29-16bdbbedaeb6

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
Standalone Prove2Me-ready child for Davie--Stothers Lemma 5.1(i).

The finite extraction works for every recursive frequency `a` in `(0,1)`.
This child supplies a legal exact frequency and proves that its rate is the
closed-form constituent target.  It deliberately does not claim a global
maximum, since attainment at this witness is all the omega-bound chain uses.
-/

private theorem normalized_two_weight_identity
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (x / (x / (x + y))) ^ (x / (x + y)) *
      (y / (y / (x + y))) ^ (y / (x + y)) = x + y := by
  have hs : 0 < x + y := add_pos hx hy
  have hxne : x ≠ 0 := ne_of_gt hx
  have hyne : y ≠ 0 := ne_of_gt hy
  have hsne : x + y ≠ 0 := ne_of_gt hs
  have hqx : x / (x / (x + y)) = x + y := by
    field_simp
  have hqy : y / (y / (x + y)) = x + y := by
    field_simp
  rw [hqx, hqy, ← Real.rpow_add hs]
  have hsum : x / (x + y) + y / (x + y) = 1 := by
    field_simp
  rw [hsum, Real.rpow_one]

theorem solution
    (E L : ℝ) (hE : 0 < E) (hL : 0 < L) :
    let a := (2 * L) / (2 * L + E ^ (2 : ℕ))
    0 < a ∧ a < 1 ∧
      4 *
          (((2 * L) / a) ^ a *
            ((E ^ (2 : ℕ)) / (1 - a)) ^ (1 - a)) =
        4 * (E ^ (2 : ℕ) + 2 * L) := by
  dsimp only
  have hx : 0 < 2 * L := mul_pos (by norm_num) hL
  have hy : 0 < E ^ (2 : ℕ) := pow_pos hE _
  have hs : 0 < 2 * L + E ^ (2 : ℕ) := add_pos hx hy
  have haPos : 0 < (2 * L) / (2 * L + E ^ (2 : ℕ)) :=
    div_pos hx hs
  have haLt : (2 * L) / (2 * L + E ^ (2 : ℕ)) < 1 :=
    (div_lt_one hs).2 (lt_add_of_pos_right (2 * L) hy)
  refine ⟨haPos, haLt, ?_⟩
  have hcomplement :
      1 - (2 * L) / (2 * L + E ^ (2 : ℕ)) =
        (E ^ (2 : ℕ)) / (2 * L + E ^ (2 : ℕ)) := by
    field_simp [ne_of_gt hs]
    ring
  rw [hcomplement]
  have h := normalized_two_weight_identity
    (2 * L) (E ^ (2 : ℕ)) hx hy
  nlinarith only [h]
