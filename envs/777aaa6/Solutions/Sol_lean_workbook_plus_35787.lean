-- Prove2me | solution 1 for lean_workbook_plus_35787
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:36:46.859619+00:00
-- url     : https://prove2.me/submissions/1458d784-0013-4c87-b856-b6efa80729a2

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (n : ℕ) : (n + 2) ^ 2 ≥ (n + 1) * (n + 3) ∧ (n + 1) * (n + 3) ≥ (n + 1) ^ 2 := by
  intros
  grind
