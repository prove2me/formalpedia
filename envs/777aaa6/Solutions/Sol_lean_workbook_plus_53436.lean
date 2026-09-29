-- Prove2me | solution 1 for lean_workbook_plus_53436
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:46:28.354341+00:00
-- url     : https://prove2.me/submissions/b9150bc7-8931-43c4-bb4a-fadd724b1a7e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z a b c : ℝ) (hx : x = 1 / b - a) (hy : y = 1 / c - b) (hz : z = 1 / a - c) : x = 1 / b - a ∧ y = 1 / c - b ∧ z = 1 / a - c := by
  (intros; simp_all)
