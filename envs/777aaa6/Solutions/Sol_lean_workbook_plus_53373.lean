-- Prove2me | solution 1 for lean_workbook_plus_53373
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:58:19.356755+00:00
-- url     : https://prove2.me/submissions/0057567c-ae44-41a5-b178-a635009b4ee1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b : ℝ) : |a| + |b| ≥ |a - b| := by
  intros
  exact abs_sub a b
