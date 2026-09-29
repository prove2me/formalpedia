-- Prove2me | solution 1 for lean_workbook_plus_420
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:29:37.857448+00:00
-- url     : https://prove2.me/submissions/7a65d376-c039-48e4-94dc-87343d484367

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x x1 x2 S P : ℂ) (hx : x ≠ x1 ∧ x ≠ x2) (hS : S = x1 + x2) (hP : P = x1 * x2) : (x - x1) * (x - x2) = x^2 - S * x + P := by
  intros
  grind
