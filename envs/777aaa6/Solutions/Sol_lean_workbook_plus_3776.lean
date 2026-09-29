-- Prove2me | solution 1 for lean_workbook_plus_3776
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:13:13.669238+00:00
-- url     : https://prove2.me/submissions/638121b8-7d02-4523-a499-00810239086b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (w z : ℂ) (hw : w + z = 1) (hz : w * z = -3) : w^2 - w - 3 = 0 ∧ z^2 - z - 3 = 0 := by
  intros
  norm_num at * <;> first | omega | nlinarith | grind
