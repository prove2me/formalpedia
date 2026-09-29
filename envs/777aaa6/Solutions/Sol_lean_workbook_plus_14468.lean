-- Prove2me | solution 1 for lean_workbook_plus_14468
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:47:14.352973+00:00
-- url     : https://prove2.me/submissions/a642144e-3fd9-4b8a-a992-6af1782a616e

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ a b : ℝ, a^2 + b^2 ≥ 2*a*b := by
  intro a b
  intros
  nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a - b)]
