-- Prove2me | solution 1 for lean_workbook_plus_52339
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:04:46.276261+00:00
-- url     : https://prove2.me/submissions/9e7069ad-3cdd-48ae-8048-125a1f776224

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (d : ℝ) (h : 2 * d - 4 ≥ d) : d ≥ 4 := by
  (intros; linarith)
