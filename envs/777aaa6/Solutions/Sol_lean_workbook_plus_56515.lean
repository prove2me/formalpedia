-- Prove2me | solution 1 for lean_workbook_plus_56515
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:42:30.513918+00:00
-- url     : https://prove2.me/submissions/e6efe343-36e9-4be8-a1bc-2b6bbfa2bd94

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution :
  ∀ a b c : ℝ,
    a^2 * b + b^2 * c + c^2 * a ≤ Real.sqrt ((a^2 + b^2 + c^2) * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2)) := by
  intro a b c
  apply Real.le_sqrt_of_sq_le
  nlinarith only [sq_nonneg (a*b*c-a*b^2), sq_nonneg (a^2*c-a*b*c), sq_nonneg (a*b*c-b*c^2)]
