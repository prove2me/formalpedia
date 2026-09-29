-- Prove2me | solution 1 for lean_workbook_plus_7451
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:59:03.82312+00:00
-- url     : https://prove2.me/submissions/bb831a54-397e-41d9-91a6-ce0254225e8b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) :
  x + Real.sqrt (x^2 + 1) - (x - Real.sqrt (x^2 + 1)) = 2 * Real.sqrt (x^2 + 1) := by
  (intros; linarith)
