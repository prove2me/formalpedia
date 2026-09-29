-- Prove2me | solution 1 for lean_workbook_plus_559
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:39:22.056465+00:00
-- url     : https://prove2.me/submissions/a39b897f-1eac-41f4-b54b-1a6aaa056a5f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) (h : |a| ≥ |b + c| ∧ |b| ≥ |c + a| ∧ |c| ≥ |a + b|) :
  a + b + c = 0 := by
  intros
  norm_num at * <;> first | omega | nlinarith | grind
