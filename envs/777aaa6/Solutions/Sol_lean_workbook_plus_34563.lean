-- Prove2me | solution 1 for lean_workbook_plus_34563
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:16:53.881272+00:00
-- url     : https://prove2.me/submissions/8d2b0f27-bd83-4717-88aa-ae3d4aaa93ca

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d : ℝ) : a * b + a * c + a * d + b * c + b * d + c * d - 6 * Real.sqrt (a * b * c * d) = (a * b + c * d - 2 * Real.sqrt (a * b * c * d)) + (a * c + b * d - 2 * Real.sqrt (a * b * c * d)) + (a * d + b * c - 2 * Real.sqrt (a * b * c * d)) := by
  (intros; linarith)
