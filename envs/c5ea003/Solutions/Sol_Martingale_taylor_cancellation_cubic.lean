-- Prove2me | solution 1 for Martingale.taylor_cancellation_cubic
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T19:11:19.945053+00:00
-- url     : https://prove2.me/submissions/a46fb4a1-bfe7-4561-a9d5-c3c7b3554f2e

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

open Finset

-- the exact algebraic cancellation: the cubic Taylor polynomials differ by ix^3/3
theorem solution (x : ℝ) :
    (1 + Complex.I * x - (x:ℂ)^2/2 - Complex.I * (x:ℂ)^3/6)
      - (1 + Complex.I * x) * (1 - (x:ℂ)^2/2)
    = Complex.I * (x:ℂ)^3 / 3 := by
  ring
