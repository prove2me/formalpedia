-- Prove2me | solution 1 for lean_workbook_plus_68529
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:12:26.262873+00:00
-- url     : https://prove2.me/submissions/6ed5725e-10e2-479b-84d6-f774d7060d1e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : x ≥ y ∧ y ≥ z) (h : (x + 1) * (y + 1) * (z + 1) ≥ 5 + x + y + z) : x * y + y * z + z * x + x * y * z ≥ 4 := by
  (intros; linarith)
