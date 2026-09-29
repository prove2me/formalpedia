-- Prove2me | solution 1 for lean_workbook_plus_69729
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T22:56:05.282277+00:00
-- url     : https://prove2.me/submissions/7759f4d9-ea72-4715-a53c-8e66db09e86b

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false

theorem solution (x : ℝ) : ⌊x⌋ ≤ x ∧ x < ⌊x⌋ + 1 := by
  exact ⟨Int.floor_le x, Int.lt_floor_add_one x⟩
