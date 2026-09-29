-- Prove2me | solution 1 for lean_workbook_plus_66754
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:29:54.293632+00:00
-- url     : https://prove2.me/submissions/87305e9a-c27a-4b4b-a2eb-98c027146ba2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : 4 * Real.sqrt 2 / 3 < x ∧ x ≤ 2) : x ∈ Set.Ioc (4 * Real.sqrt 2 / 3) 2 := by
  (intros; simp_all)
