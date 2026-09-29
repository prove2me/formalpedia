-- Prove2me | solution 1 for lean_workbook_plus_28517
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:52.256354+00:00
-- url     : https://prove2.me/submissions/80e676fa-82c2-4fcb-ab0d-8be3ac1ec551

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  intros
  grind
