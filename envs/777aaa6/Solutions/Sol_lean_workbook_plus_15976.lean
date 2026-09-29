-- Prove2me | solution 1 for lean_workbook_plus_15976
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:12:56.128609+00:00
-- url     : https://prove2.me/submissions/936c1383-45d4-45c4-9620-ed4d097286e9

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a : ℝ) : 2021 = 3 * a ↔ a = 2021/3 := by
  intros
  norm_num at * <;> first | omega | nlinarith | grind
