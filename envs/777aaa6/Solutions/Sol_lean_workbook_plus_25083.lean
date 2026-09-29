-- Prove2me | solution 1 for lean_workbook_plus_25083
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:35:05.520027+00:00
-- url     : https://prove2.me/submissions/5ccce043-6ec8-41a9-b06e-eea413e6fb76

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {A B C : ℂ} (h : A + B + C = 0) : A ^ 3 + B ^ 3 + C ^ 3 = 3 * A * B * C := by
  intros
  grind
