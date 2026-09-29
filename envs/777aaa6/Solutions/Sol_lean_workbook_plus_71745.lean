-- Prove2me | solution 1 for lean_workbook_plus_71745
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:51:29.195607+00:00
-- url     : https://prove2.me/submissions/08f3e8cb-fbc0-4e69-a4ee-5bc9e2748f12

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (u v w x y z : ℝ) : (u^2 + v^2 + w^2 + 3 * (x^2 + y^2 + z^2) = 6 ∧ u * x + v * y + w * z = 2) ↔ (u^2 + v^2 + w^2 + 3 * (x^2 + y^2 + z^2) = 6 ∧ u * x + v * y + w * z = 2) := by
  norm_num
