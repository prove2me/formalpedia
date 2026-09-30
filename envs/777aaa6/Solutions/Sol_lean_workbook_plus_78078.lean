-- Prove2me | solution 1 for lean_workbook_plus_78078
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:34:58.002969+00:00
-- url     : https://prove2.me/submissions/f9d0019f-a4d8-4a92-b005-364066f49587

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (hx : a > 0 ∧ b > 0 ∧ c > 0)
    (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) :
    a ^ 2 + b ^ 2 + c ^ 2 < 2 * (a * b + b * c + c * a) := by
  have ha' := mul_lt_mul_of_pos_left hbc hx.1
  have hb' := mul_lt_mul_of_pos_left hca hx.2.1
  have hc' := mul_lt_mul_of_pos_left hab hx.2.2
  nlinarith

#print axioms solution
