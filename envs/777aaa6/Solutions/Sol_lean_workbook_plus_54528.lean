-- Prove2me | solution 1 for lean_workbook_plus_54528
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:01:36.443996+00:00
-- url     : https://prove2.me/submissions/6269fcb3-6a07-465b-a64a-ce72d4d2a943

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∀ a b c : ℝ, a * b * c = 1 → a ^ 4 + b ^ 4 + c ^ 4 + 3 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + a ^ 2 * c ^ 2) ≥ 2 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * a) + 2 * (a * b ^ 3 + b * c ^ 3 + c * a ^ 3) := by
  intro a b c
  intro h
  clear h
  nlinarith [sq_nonneg ((a - b)^2), sq_nonneg ((a - c)^2), sq_nonneg ((b - c)^2)]
