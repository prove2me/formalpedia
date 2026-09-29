-- Prove2me | solution 1 for lean_workbook_plus_74401
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:52:10.503863+00:00
-- url     : https://prove2.me/submissions/3dff921f-4686-4abd-bce9-99205af1dd80

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) : (∀ x, f x = -f (-x)) ↔ ∀ x, f x = -f (-x) := by
  norm_num
