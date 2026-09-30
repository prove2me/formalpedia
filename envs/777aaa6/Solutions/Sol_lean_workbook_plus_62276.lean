-- Prove2me | solution 1 for lean_workbook_plus_62276
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:50:59.770148+00:00
-- url     : https://prove2.me/submissions/6fea2767-471a-4ebe-be7d-7ad01b2165f4

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c d : ℝ) (h1 : a ≥ b ∧ b ≥ 0) (h2 : c ≥ d ∧ d ≥ 0)
    (h3 : a ≤ c) (h4 : a * b ≤ c * d) : a + b ≤ c + d := by
  by_contra hsum
  have hs : c + d < a + b := lt_of_not_ge hsum
  have hbd : d < b := by linarith
  have had : d < a := hbd.trans_le h1.1
  have hp := mul_pos (sub_pos.mpr had) (sub_pos.mpr hbd)
  have hr := mul_nonneg h2.2 (show 0 ≤ a + b - c - d by linarith)
  nlinarith

#print axioms solution
