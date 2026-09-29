-- Prove2me | solution 1 for lean_workbook_plus_7901
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:38:48.170299+00:00
-- url     : https://prove2.me/submissions/d299ddd9-c64f-4834-8437-a78fde01d8b3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) : (a^2 + b^2)/2 ≥ a * b ∧ (b^2 + c^2)/2 ≥ b * c ∧ (c^2 + a^2)/2 ≥ c * a := by
  constructor
  · nlinarith [sq_nonneg (a-b)]
  · constructor
    · nlinarith [sq_nonneg (b-c)]
    · nlinarith [sq_nonneg (c-a)]
