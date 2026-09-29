-- Prove2me | solution 1 for lean_workbook_plus_9252
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:20:29.649707+00:00
-- url     : https://prove2.me/submissions/7ec0de7b-6fc3-4a39-932e-7b8c73cd1828

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  intros
  grind
