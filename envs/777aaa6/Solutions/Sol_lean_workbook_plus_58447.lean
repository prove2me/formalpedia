-- Prove2me | solution 1 for lean_workbook_plus_58447
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:01:19.574796+00:00
-- url     : https://prove2.me/submissions/98a915ed-f202-4740-9d48-dd8d22a405e3

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (t : ℝ) : t^2 + 308 * t + 23700 = 0 ↔ t = -150 ∨ t = -158 := by
  intros
  grind
