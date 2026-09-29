-- Prove2me | solution 1 for lean_workbook_plus_28817
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:38:34.89171+00:00
-- url     : https://prove2.me/submissions/f7923acd-3ce7-42df-b75a-3fce9f5e95c0

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ‖3 + 4 * Complex.I‖ = 5 := by
  rw [Complex.norm_def]
  norm_num [Complex.normSq]
