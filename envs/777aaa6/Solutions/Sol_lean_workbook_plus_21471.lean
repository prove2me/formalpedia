-- Prove2me | solution 1 for lean_workbook_plus_21471
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:25:04.500866+00:00
-- url     : https://prove2.me/submissions/c4cf2e21-c4e9-498c-ad84-6c00bbd99cf6

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (u v : ℝ) (huv : u < v) : ∃ q : ℚ, u < q ∧ q < v := by
  intros
  exact exists_rat_btwn huv
