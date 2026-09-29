-- Prove2me | solution 1 for lean_workbook_plus_3625
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:40:01.087642+00:00
-- url     : https://prove2.me/submissions/daa4681b-ae6e-4779-8c73-6d7325f617c6

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (r : ℝ) : (1 - 2 * r ≥ 0 ∧ r ≤ 1 / 2) ↔ r ≤ 1 / 2 := by
  intros
  grind
