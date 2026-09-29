-- Prove2me | solution 1 for lean_workbook_plus_31182
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:54:05.21381+00:00
-- url     : https://prove2.me/submissions/a431f5f1-4f17-4f72-91a6-3d75abf7f595

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y: ℝ) : (x + 1) * (y + 1) ≥ 4 * Real.sqrt (x * y) ↔ x * y + x + y + 1 ≥ 4 * Real.sqrt (x * y) := by
  (intros; ring)
