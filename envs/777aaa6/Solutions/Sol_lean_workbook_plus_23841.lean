-- Prove2me | solution 1 for lean_workbook_plus_23841
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:47:00.548565+00:00
-- url     : https://prove2.me/submissions/ecbf8074-9264-4ed3-aed2-5fe20bf1cd3e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c s A B C : ℕ → ℕ) (hA : A = b + c) (hB : B = a + c) (hC : C = a + b) (hs : s = a + b + c) : a^2 + b^2 + c^2 + s^2 = A^2 + B^2 + C^2 := by
  intros
  grind
