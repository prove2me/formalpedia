-- Prove2me | solution 1 for RybinAI2026.P01.diagonal_pair_contraction_from_envelopes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T01:35:38.397323+00:00
-- url     : https://prove2.me/submissions/c068a094-7d93-4d2f-aa53-e793058bb08c

import Mathlib
import Theorems.Thm_RybinAI2026_P01_diagonal_pair_coefficient_bound

theorem solution
    {x y A B z r s : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : A ^ 2 = x * (1 - y)) (hB : B ^ 2 = y * (1 - x))
    (hz : 0 ≤ z) (hr0 : 0 ≤ r) (hs0 : 0 ≤ s)
    (hlow : x + y ≤ 1 → r ^ 2 ≤ A ^ 2 ∧ s ^ 2 ≤ B ^ 2)
    (hhigh : 1 < x + y →
      r ≤ (x + A * z) / (1 + z) ∧ s ≤ (B + y * z) / (1 + z)) :
    r ^ 2 + s ^ 2 ≤ 1 := by
  by_cases h : x + y ≤ 1
  · obtain ⟨hr, hs⟩ := hlow h
    have hxy : 0 ≤ x * y := mul_nonneg hx0 hy0
    have hab : A ^ 2 + B ^ 2 ≤ 1 := by
      rw [hA, hB]
      nlinarith [hxy]
    nlinarith
  · have hsum : 1 < x + y := lt_of_not_ge h
    obtain ⟨hr, hs⟩ := hhigh hsum
    have hcoef :=
      RybinAI2026.P01.diagonal_pair_coefficient_bound
        hx0 hx1 hy0 hy1 hA0 hB0 hA hB hz
    have hz1 : 0 < 1 + z := by linarith
    have hrbound : 0 ≤ (x + A * z) / (1 + z) :=
      div_nonneg (add_nonneg hx0 (mul_nonneg hA0 hz)) (le_of_lt hz1)
    have hsbound : 0 ≤ (B + y * z) / (1 + z) :=
      div_nonneg (add_nonneg hB0 (mul_nonneg hy0 hz)) (le_of_lt hz1)
    have hrsq : r ^ 2 ≤ ((x + A * z) / (1 + z)) ^ 2 :=
      (sq_le_sq₀ hr0 hrbound).2 hr
    have hssq : s ^ 2 ≤ ((B + y * z) / (1 + z)) ^ 2 :=
      (sq_le_sq₀ hs0 hsbound).2 hs
    have hden : 0 < (1 + z) ^ 2 := sq_pos_of_pos hz1
    have hfrac :
        ((x + A * z) / (1 + z)) ^ 2 + ((B + y * z) / (1 + z)) ^ 2 ≤ 1 := by
      calc
        _ = ((x + A * z) ^ 2 + (B + y * z) ^ 2) / (1 + z) ^ 2 := by
          field_simp [hz1.ne']
        _ ≤ 1 := (div_le_iff₀ hden).2 (by nlinarith [hcoef])
    nlinarith
