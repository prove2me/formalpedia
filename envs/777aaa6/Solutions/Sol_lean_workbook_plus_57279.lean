-- Prove2me | solution 1 for lean_workbook_plus_57279
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:50:03.968169+00:00
-- url     : https://prove2.me/submissions/aa6e5ea0-5273-42d6-9211-bf99c5916a39

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : 3 * x - 5 < 7 ↔ x < 4 := by
  intros
  grind
