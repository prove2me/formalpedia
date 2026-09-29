-- Prove2me | solution 1 for lean_workbook_plus_43478
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:39:37.331598+00:00
-- url     : https://prove2.me/submissions/0f03bc58-c2b9-403e-8c65-b32b248fa408

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z : ℝ) : (9*x+8*y+7*z=987 ∧ 3*x+4*y+2*z=342 ∧ 2*x+5*y+8*z=258) ↔ x=100 ∧ y=10 ∧ z=1 := by
  intros
  grind
