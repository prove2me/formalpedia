-- Prove2me | solution 1 for lean_workbook_plus_17089
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:48:34.34327+00:00
-- url     : https://prove2.me/submissions/ec181a43-2e19-442e-a167-dbb017f05817

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b : ℝ) : |a * b| = |a| * |b| ∧  |b - a| = |a - b| := by
  exact ⟨abs_mul a b, abs_sub_comm b a⟩
