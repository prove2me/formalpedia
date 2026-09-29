-- Prove2me | solution 1 for lean_workbook_plus_38235
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:46:42.463784+00:00
-- url     : https://prove2.me/submissions/624f1546-cb5b-4550-b6ad-b9a6b727a2b9

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ n : ℤ, Even n → Even (n^2) := by
  intro n
  intros
  grind
