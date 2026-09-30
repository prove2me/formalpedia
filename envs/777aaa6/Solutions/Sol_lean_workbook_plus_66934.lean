-- Prove2me | solution 1 for lean_workbook_plus_66934
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:46:53.945391+00:00
-- url     : https://prove2.me/submissions/609b657f-8f13-48d8-8526-cf6f48717db8

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

theorem solution (a b : ℤ) (h : a^2 + 3 * b^2 ≡ 0 [ZMOD 4]) :
    a ≡ b [ZMOD 2] := by
  have hm : a ^ 2 + 3 * b ^ 2 ≡ 0 [ZMOD 2] :=
    Int.ModEq.of_dvd (by norm_num : (2 : ℤ) ∣ 4) h
  have ha0 := Int.emod_nonneg a (by decide : (2 : ℤ) ≠ 0)
  have ha1 := Int.emod_lt_of_pos a (by decide : (0 : ℤ) < 2)
  have hb0 := Int.emod_nonneg b (by decide : (2 : ℤ) ≠ 0)
  have hb1 := Int.emod_lt_of_pos b (by decide : (0 : ℤ) < 2)
  interval_cases ha : a % 2 <;> interval_cases hb : b % 2 <;>
    simp_all [Int.ModEq, pow_two, Int.add_emod, Int.mul_emod]

#print axioms solution
