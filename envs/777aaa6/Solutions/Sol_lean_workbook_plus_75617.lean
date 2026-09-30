-- Prove2me | solution 1 for lean_workbook_plus_75617
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:42:37.858288+00:00
-- url     : https://prove2.me/submissions/9a14b9ce-be96-4c37-b7cb-dfec8125ebd3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (ha : a + b > c) (hb : a + c > b) (hc : b + c > a) :
    (a ^ 3 + b ^ 3 - c ^ 3) / (a + b - c) ≤ (3 / 2) * (a ^ 2 + b ^ 2 + c ^ 2) := by
  have ha' : 0 < a := by linarith
  have hb' : 0 < b := by linarith
  have hc' : 0 < c := by linarith
  have hden : 0 < a + b - c := by linarith
  apply (div_le_iff₀ hden).mpr
  have hcube : 0 ≤ (a + b - c) ^ 3 := by positivity
  have hprod : 0 ≤ a * b * c := by positivity
  nlinarith

#print axioms solution
