-- Prove2me | solution 1 for lean_workbook_plus_36147
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:04:59.70727+00:00
-- url     : https://prove2.me/submissions/ec228cd3-537e-4419-999c-4ff93af85c7a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : (6 : ℝ) < 4 * Real.sqrt 3 → (7 - 4 * Real.sqrt 3) < 1 := by
  (intros; linarith)
