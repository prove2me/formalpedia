-- Prove2me | solution 1 for lean_workbook_plus_45241
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:54:19.27857+00:00
-- url     : https://prove2.me/submissions/a0a2362b-9384-414e-b922-b819f395f7ea

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : x ≥ Int.floor x := by
  intros
  exact?
