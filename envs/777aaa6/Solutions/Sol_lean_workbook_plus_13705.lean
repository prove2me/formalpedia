-- Prove2me | solution 1 for lean_workbook_plus_13705
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:19:16.728825+00:00
-- url     : https://prove2.me/submissions/0fe1215f-cd13-467b-a543-fa11f87fff66

import Mathlib

theorem solution (x : ℝ) (h₀ : 1 ≤ x ∧ x ≤ 3 / 2) :
    x^3 + (8 * x^3) / (2 * x - 1)^3 ≤ 9 := by
  have hx0 : 0 ≤ x := by linarith [h₀.1]
  have hden : 0 < 2 * x - 1 := by linarith [h₀.1]
  have hfactor : 0 ≤ (x - 1) * (3 - 2 * x) :=
    mul_nonneg (by linarith [h₀.1]) (by linarith [h₀.2])
  have hy : 2 * x / (2 * x - 1) ≤ 3 - x := by
    apply (div_le_iff₀ hden).2
    nlinarith only [hfactor]
  have hy0 : 0 ≤ 2 * x / (2 * x - 1) := by positivity
  have hcube : (2 * x / (2 * x - 1)) ^ 3 ≤ (3 - x) ^ 3 :=
    pow_le_pow_left₀ hy0 hy 3
  have hrewrite : (8 * x ^ 3) / (2 * x - 1) ^ 3 =
      (2 * x / (2 * x - 1)) ^ 3 := by
    rw [div_pow]
    ring
  rw [hrewrite]
  have hlast : 0 ≤ (x - 1) * (2 - x) :=
    mul_nonneg (by linarith [h₀.1]) (by linarith [h₀.2])
  nlinarith only [hcube, hlast]

#print axioms solution
