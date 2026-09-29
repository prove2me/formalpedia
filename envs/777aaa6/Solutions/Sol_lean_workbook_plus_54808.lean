-- Prove2me | solution 1 for lean_workbook_plus_54808
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:00:58.639041+00:00
-- url     : https://prove2.me/submissions/09d5fdbf-8e87-4d52-ad29-71de50d1f3b6

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b c : ℝ} :
  (a^2 + b^2)^2 ≥ (a + b + c) * (a + b - c) * (b + c - a) * (c + a - b) ↔
  (a^2 + b^2 - c^2)^2 + (a^2 - b^2)^2 ≥ 0 := by
  intros
  grind
