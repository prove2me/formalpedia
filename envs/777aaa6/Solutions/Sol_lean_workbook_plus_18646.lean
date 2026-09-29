-- Prove2me | solution 1 for lean_workbook_plus_18646
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:10.599622+00:00
-- url     : https://prove2.me/submissions/98ebc934-04dc-443b-a0d2-9b1722cb25a1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : 1981 ∣ 145 ^ 1981 + 3114 * 138 ^ 1981 := by
  intros
  norm_num at * <;> first | omega | nlinarith | grind
