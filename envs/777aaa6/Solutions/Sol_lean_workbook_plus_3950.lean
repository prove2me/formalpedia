-- Prove2me | solution 1 for lean_workbook_plus_3950
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:42:37.291361+00:00
-- url     : https://prove2.me/submissions/b0b25b78-1b26-4ed4-b2b3-db936fddf56c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (n k : ℤ)
  (h₀ : 0 ≤ k ∧ k ≤ 2) :
  (3 * n + k)^3 % 9 = k^3 % 9 := by
  intros
  grind
