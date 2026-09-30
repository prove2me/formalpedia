-- Prove2me | solution 1 for lean_workbook_plus_76132
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:12:32.977201+00:00
-- url     : https://prove2.me/submissions/1bec8c10-ed51-4803-b637-442d10e36783

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

theorem distinct_triple_rational_identity {K : Type*} [Field K]
    (a b c : K) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    a ^ 3 / (b - c) ^ 2 + b ^ 3 / (c - a) ^ 2 + c ^ 3 / (a - b) ^ 2 =
      a + b + c + (a / (b - c) + b / (c - a) + c / (a - b)) *
        (a ^ 2 / (b - c) + b ^ 2 / (c - a) + c ^ 2 / (a - b)) := by
  field_simp [sub_ne_zero.mpr hab, sub_ne_zero.mpr hbc, sub_ne_zero.mpr hca] <;> ring

theorem solution (a b c : ℝ) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a) :
    a ^ 3 / (b - c) ^ 2 + b ^ 3 / (c - a) ^ 2 + c ^ 3 / (a - b) ^ 2 =
      a + b + c + (a / (b - c) + b / (c - a) + c / (a - b)) *
        (a ^ 2 / (b - c) + b ^ 2 / (c - a) + c ^ 2 / (a - b)) :=
  distinct_triple_rational_identity a b c hab hbc hca

#print axioms solution
#print axioms distinct_triple_rational_identity
