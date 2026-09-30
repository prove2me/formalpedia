-- Prove2me | solution 1 for lean_workbook_plus_27477
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:54:22.300547+00:00
-- url     : https://prove2.me/submissions/90c6f9d2-1859-4443-99a5-45c2f008cae2

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false

theorem solution (a b : Real) (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) :
    a / (2 * b + 5) + b / (2 * a + 5) ≤ 2 / 7 := by
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  have hau : 0 ≤ 1 - a := by linarith
  have hbu : 0 ≤ 1 - b := by linarith
  have hda : 2 * a + 5 ≠ 0 := by positivity
  have hdb : 2 * b + 5 ≠ 0 := by positivity
  have hid : 2 / 7 - (a / (2 * b + 5) + b / (2 * a + 5)) =
      (14 * a * (1 - a) + 14 * b * (1 - b) + 21 * (1 - a) + 21 * (1 - b) +
        8 * (1 - a) * (1 - b)) / (7 * (2 * a + 5) * (2 * b + 5)) := by
    field_simp
    ring
  have hn : 0 ≤ 14 * a * (1 - a) + 14 * b * (1 - b) + 21 * (1 - a) +
      21 * (1 - b) + 8 * (1 - a) * (1 - b) := by positivity
  have hd : 0 < 7 * (2 * a + 5) * (2 * b + 5) := by positivity
  have hdiff : 0 ≤ 2 / 7 - (a / (2 * b + 5) + b / (2 * a + 5)) := by
    rw [hid]
    exact div_nonneg hn hd.le
  linarith

#print axioms solution
