-- Prove2me | solution 1 for lean_workbook_plus_55651
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:05:26.999947+00:00
-- url     : https://prove2.me/submissions/4ffaddcb-3400-4ad6-9533-90e308e07d66

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

theorem solution (x y : ℝ) (h1 : 0 < y ∧ y < x ∧ x ≤ 3)
    (h2 : x + y ≤ 5) : x^2 + y^2 ≤ 13 := by
  rcases h1 with ⟨hy, hyx, hx⟩
  by_cases hy2 : y ≤ 2
  · have hxx : 0 ≤ x * (3 - x) := mul_nonneg (by linarith) (by linarith)
    have hyy : 0 ≤ y * (2 - y) := mul_nonneg hy.le (by linarith)
    nlinarith
  · have hxx : (x - 2) * (x - 3) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    have hyy : (y - 2) * (y - 3) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    nlinarith
