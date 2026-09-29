-- Prove2me | solution 1 for lean_workbook_plus_52990
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:03:41.201503+00:00
-- url     : https://prove2.me/submissions/1ccb8c05-ab0a-4cb0-8b7e-3ce8581236d4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (h₁ : 2 < x) (h₂ : x ≤ 3) : -(x - 3) - (x - 4) = -2 * x + 7 := by
  (intros; linarith)
