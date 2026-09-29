-- Prove2me | solution 1 for lean_workbook_plus_58650
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:38:55.513191+00:00
-- url     : https://prove2.me/submissions/9af0a708-f12f-47c6-8171-d38ee89814cc

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {f : ℝ → ℝ} (hf : Function.Injective f) (h : f (f 0) = f 0) : f 0 = 0 := by
  intros
  aesop (config := {maxRuleApplications := 120})
