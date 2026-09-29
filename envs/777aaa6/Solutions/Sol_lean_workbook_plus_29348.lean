-- Prove2me | solution 1 for lean_workbook_plus_29348
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:13:24.312595+00:00
-- url     : https://prove2.me/submissions/7972801b-3772-4a16-ad06-d4e984f1d35d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : 2*x - 5 < 15 ↔ x < 10 := by
  intros
  norm_num at * <;> first | omega | nlinarith | grind
