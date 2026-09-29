-- Prove2me | solution 1 for lean_workbook_plus_47302
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:41:27.009466+00:00
-- url     : https://prove2.me/submissions/de2978bf-8713-4628-af15-d969573b7fa7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) : |a| - |b| ≤ |a + b| ∧ |a + b| ≤ |a| + |b| := by
  intros
  grind
