-- Prove2me | solution 1 for lean_workbook_plus_14427
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:47:32.284676+00:00
-- url     : https://prove2.me/submissions/e05c98b5-0c67-4b53-902b-16cbbab36c30

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (n : ℕ)
  (h₀ : 0 < n) :
  ((n + 1) * (n + 2) - (n + 1)) = (n + 1)^2 := by
  intros
  grind
