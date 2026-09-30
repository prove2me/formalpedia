-- Prove2me | solution 1 for lean_workbook_plus_2640
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:39:49.119437+00:00
-- url     : https://prove2.me/submissions/a5862faf-bc4a-4367-b314-0621e22a7f67

import Mathlib
set_option autoImplicit false

theorem solution (a b c : ℝ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 1): a^3 + b^3 + c^3 >= a * b + b * c + a * c   := by
  rcases ha with ⟨ha, hb, hc, habc⟩
  have hmean := Real.geom_mean_le_arith_mean3_weighted
    (w₁ := (1 : ℝ) / 3) (w₂ := (1 : ℝ) / 3) (w₃ := (1 : ℝ) / 3)
    (p₁ := a) (p₂ := b) (p₃ := c)
    (by norm_num) (by norm_num) (by norm_num)
    ha.le hb.le hc.le (by norm_num)
  have hroots : a ^ ((1 : ℝ) / 3) * b ^ ((1 : ℝ) / 3) * c ^ ((1 : ℝ) / 3) = 1 := by
    rw [← Real.mul_rpow ha.le hb.le,
      ← Real.mul_rpow (mul_nonneg ha.le hb.le) hc.le, habc, Real.one_rpow]
  rw [hroots] at hmean
  have hsum : (3 : ℝ) ≤ a + b + c := by linarith only [hmean]
  have hD1 : (0 : ℝ) ≤ (a - b) ^ 2 * (a + b) :=
    mul_nonneg (sq_nonneg (a - b)) (add_nonneg ha.le hb.le)
  have hD2 : (0 : ℝ) ≤ (b - c) ^ 2 * (b + c) :=
    mul_nonneg (sq_nonneg (b - c)) (add_nonneg hb.le hc.le)
  have hD3 : (0 : ℝ) ≤ (c - a) ^ 2 * (c + a) :=
    mul_nonneg (sq_nonneg (c - a)) (add_nonneg hc.le ha.le)
  have hS : (0 : ℝ) ≤ (a + b + c - 3) * (a ^ 2 + b ^ 2 + c ^ 2) :=
    mul_nonneg (sub_nonneg.mpr hsum)
      (add_nonneg (add_nonneg (sq_nonneg a) (sq_nonneg b)) (sq_nonneg c))
  have hcertificate :
      6 * (a ^ 3 + b ^ 3 + c ^ 3 - (a * b + b * c + a * c)) =
        2 * ((a - b) ^ 2 * (a + b)) + 2 * ((b - c) ^ 2 * (b + c)) +
          2 * ((c - a) ^ 2 * (c + a)) +
          2 * ((a + b + c - 3) * (a ^ 2 + b ^ 2 + c ^ 2)) +
          3 * (a - b) ^ 2 + 3 * (b - c) ^ 2 + 3 * (c - a) ^ 2 := by ring
  have hgap : (0 : ℝ) ≤ 6 * (a ^ 3 + b ^ 3 + c ^ 3 - (a * b + b * c + a * c)) := by
    rw [hcertificate]
    linarith only [hD1, hD2, hD3, hS, sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  linarith only [hgap]

#print axioms solution
