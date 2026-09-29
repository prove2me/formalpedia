-- Prove2me | solution 1 for mme_Ctensor_balanced_weight_sqrt_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T02:38:16.372056+00:00
-- url     : https://prove2.me/submissions/2dc09b3d-0118-4031-a549-1991d3c5ee12

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Stirling
import Theorems.Thm_mme_Ctensor_balanced_word_card
import Theorems.Thm_mme_Ctensor_balanced_count_matching_sqrt_loss

open BigOperators Filter

set_option autoImplicit false

theorem solution
    (H volume : ℕ) (hH : 0 < H) (hvolume : 0 < volume)
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        let R : ℕ := H * m
        let W : ℕ :=
          Nat.card
            {w : Fin R → Fin H // ∀ h,
              Fintype.card {j // w j = h} = m}
        (((H : ℝ) ^ 2 *
              (((volume ^ 3 : ℕ) : ℝ) ^ tau)) ^ R) *
            Real.exp
              (-C * Real.sqrt (((R + 1 : ℕ) : ℝ))) ≤
          ((W : ℝ) ^ 2 *
              Real.exp
                (-100 * Real.sqrt
                  (Real.log (((W + 1 : ℕ) : ℝ))))) *
            (((volume ^ (3 * R) : ℕ) : ℝ) ^ tau) := by
  obtain ⟨C, hC, hcount⟩ :=
    mme_Ctensor_balanced_count_matching_sqrt_loss H hH
  refine ⟨C, hC, ?_⟩
  filter_upwards [hcount] with m hm
  dsimp only at hm ⊢
  let R : ℕ := H * m
  let W : ℕ :=
    Nat.card
      {w : Fin R → Fin H // ∀ h,
        Fintype.card {j // w j = h} = m}
  let q : ℝ := (((volume ^ (3 * R) : ℕ) : ℝ) ^ tau)
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hvolumePow :
      ((((volume ^ 3 : ℕ) : ℝ) ^ tau) ^ R) = q := by
    dsimp [q]
    push_cast
    rw [← Real.rpow_mul_natCast (by positivity) tau R]
    rw [← Real.rpow_natCast_mul (by positivity) 3 (tau * R)]
    rw [← Real.rpow_natCast_mul (by positivity) (3 * R) tau]
    congr 1
    push_cast
    ring
  have hbase :
      (((H : ℝ) ^ 2 *
          (((volume ^ 3 : ℕ) : ℝ) ^ tau)) ^ R) =
        (H : ℝ) ^ (2 * R) * q := by
    rw [mul_pow, hvolumePow]
    rw [← pow_mul]
  change
    (((H : ℝ) ^ 2 *
          (((volume ^ 3 : ℕ) : ℝ) ^ tau)) ^ R) *
        Real.exp (-C * Real.sqrt (((R + 1 : ℕ) : ℝ))) ≤
      ((W : ℝ) ^ 2 *
          Real.exp
            (-100 * Real.sqrt (Real.log (((W + 1 : ℕ) : ℝ))))) * q
  rw [hbase]
  calc
    ((H : ℝ) ^ (2 * R) * q) *
          Real.exp (-C * Real.sqrt (((R + 1 : ℕ) : ℝ))) =
        ((H : ℝ) ^ (2 * R) *
          Real.exp (-C * Real.sqrt (((R + 1 : ℕ) : ℝ)))) * q := by ring
    _ ≤ ((W : ℝ) ^ 2 *
          Real.exp
            (-100 * Real.sqrt (Real.log (((W + 1 : ℕ) : ℝ))))) * q := by
      exact mul_le_mul_of_nonneg_right (by simpa [R, W] using hm) hq
