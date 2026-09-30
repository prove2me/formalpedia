-- Prove2me | solution 1 for lean_workbook_plus_81968
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:06:05.205727+00:00
-- url     : https://prove2.me/submissions/5db4e2ab-eddf-4b72-972d-6a90c53d09a7

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (a b c : ℝ) (h1 : |a| ≥ |b + c|) (h2 : |b| ≥ |c + a|)
    (h3 : |c| ≥ |a + b|) : a + b + c = 0 := by
  have h1' : (b + c) ^ 2 ≤ a ^ 2 := sq_le_sq.mpr h1
  have h2' : (c + a) ^ 2 ≤ b ^ 2 := sq_le_sq.mpr h2
  have h3' : (a + b) ^ 2 ≤ c ^ 2 := sq_le_sq.mpr h3
  have hs : (a + b + c) ^ 2 ≤ 0 := by nlinarith
  exact sq_eq_zero_iff.mp (le_antisymm hs (sq_nonneg _))
