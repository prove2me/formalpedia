-- Prove2me | solution 1 for lean_workbook_plus_10448
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:59:45.621717+00:00
-- url     : https://prove2.me/submissions/113e3043-2273-4671-8d57-f53a4e325210

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) (h₁ : 0 < a ∧ a ≤ b ∧ b ≤ c) :
  c - a ≥ 0 ∧ c - b ≥ 0 ∧ b - a ≥ 0 := by
  intros
  grind
