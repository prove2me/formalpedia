-- Prove2me | solution 1 for lean_workbook_plus_40975
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:46:25.664484+00:00
-- url     : https://prove2.me/submissions/23f0125e-d205-4e1c-895d-0d940807223d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) (h1 : a + b ≥ 0) (h2 : b + c ≥ 0) (h3 : c + a ≥ 0) : a + b + c ≥ (|a| + |b| + |c|) / 3 := by
  intros
  grind
