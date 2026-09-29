-- Prove2me | solution 1 for lean_workbook_plus_35274
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:12:52.161491+00:00
-- url     : https://prove2.me/submissions/fb48b990-6544-49af-9645-29101598bc30

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) (h : a + b + c = 2) :
  |a| - |b| - |c| ≤ 2 := by
  intros
  norm_num at * <;> first | omega | nlinarith | grind
