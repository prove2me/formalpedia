-- Prove2me | solution 1 for lean_workbook_plus_75005
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:15:38.478705+00:00
-- url     : https://prove2.me/submissions/84e47864-d5dc-453c-9e68-94fa84a185e9

import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

private theorem sum_ge_three (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (habc : a * b * c = 1) : 3 ≤ a + b + c := by
  have h := Real.geom_mean_le_arith_mean3_weighted
    (w₁ := (1 / 3 : ℝ)) (w₂ := (1 / 3 : ℝ)) (w₃ := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) ha hb hc (by norm_num)
  rw [← Real.mul_rpow ha hb, ← Real.mul_rpow (mul_nonneg ha hb) hc,
    habc, Real.one_rpow] at h
  linarith

theorem solution (a b c : ℝ)
    (h1 : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a * b * c = 1) :
    (1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2) ≥
      (1 + a) * (1 + b) * (1 + c) := by
  obtain ⟨ha, hb, hc, habc⟩ := h1
  have hs := sum_ge_three a b c ha hb hc habc
  have hp := sum_ge_three (a * b) (b * c) (c * a)
    (mul_nonneg ha hb) (mul_nonneg hb hc) (mul_nonneg hc ha) (by
      calc
        a * b * (b * c) * (c * a) = (a * b * c) ^ 2 := by ring
        _ = 1 := by rw [habc]; norm_num)
  have hs2 : 0 ≤ (a + b + c) ^ 2 - 3 * (a + b + c) := by
    nlinarith [sq_nonneg (a + b + c - 3)]
  have hp2 : 0 ≤ (a * b + b * c + c * a) ^ 2 - 3 * (a * b + b * c + c * a) := by
    nlinarith [sq_nonneg (a * b + b * c + c * a - 3)]
  have identity :
      (1 + a ^ 2) * (1 + b ^ 2) * (1 + c ^ 2) -
          (1 + a) * (1 + b) * (1 + c) =
        ((a + b + c) ^ 2 - 3 * (a + b + c)) +
        ((a * b + b * c + c * a) ^ 2 - 3 * (a * b + b * c + c * a)) +
        (a * b * c - 1) * (a * b * c - 2 * (a + b + c)) := by ring
  rw [habc, sub_self, zero_mul, add_zero] at identity
  linarith

#print axioms solution
