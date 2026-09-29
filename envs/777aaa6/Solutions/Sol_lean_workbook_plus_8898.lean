-- Prove2me | solution 1 for lean_workbook_plus_8898
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:48:49.54354+00:00
-- url     : https://prove2.me/submissions/24d1120f-1634-4e50-b9a6-2a1e6ab75008

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (2 - a) / (2 + a) + (2 - b) / (2 + b) + (2 - c) / (2 + c) ≥ 15 / 7 ↔ 4 / (2 + a) + 4 / (2 + b) + 4 / (2 + c) ≥ 36 / 7 := by
  intros
  grind
