-- Prove2me | solution 1 for lean_workbook_plus_2484
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:45:36.633913+00:00
-- url     : https://prove2.me/submissions/307c46dd-c4a1-414c-a1d0-ee4a961b3c27

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℤ) (h₁ : a + b + c = 96) (h₂ : a = 6 * c) (h₃ : c = b - 40) : |a - b| = 5 := by
  intros
  grind
