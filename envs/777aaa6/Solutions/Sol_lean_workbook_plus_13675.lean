-- Prove2me | solution 1 for lean_workbook_plus_13675
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:20.149437+00:00
-- url     : https://prove2.me/submissions/d05b0c55-33c2-4326-a03b-d2b4551aad3f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : (Real.sqrt 5 + 3 + Real.sqrt 7) * (Real.sqrt 5 + 3 - Real.sqrt 7) = 7 + 6 * Real.sqrt 5 := by
  intros
  grind
