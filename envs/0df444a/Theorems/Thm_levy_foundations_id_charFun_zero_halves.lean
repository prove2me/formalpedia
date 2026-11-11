-- Prove2me | Theorems.Thm_levy_foundations_id_charFun_zero_halves
-- name    : levy_foundations_id_charFun_zero_halves
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T07:54:52.730409+00:00
-- url     : https://prove2.me/theorems/3e9b981a-9f4d-4c56-9949-8f142663efb6
-- title:
--   Dyadic zero propagation for infinitely divisible characteristic functions
-- statement:
--   For an infinitely divisible probability law on ℝ, if the characteristic function vanishes at 2ξ then it vanishes at ξ. The proof takes roots of every positive order and uses the elementary positive-definiteness bound 2|φν(ξ)|² ≤ 1+|φν(2ξ)| for characteristic functions φν; with the right side equal to 1, n-th powers force |φμ(ξ)| to zero.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isInfinitelyDivisible

open MeasureTheory ProbabilityTheory

theorem levy_foundations_id_charFun_zero_halves
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : LevyFoundations.isInfinitelyDivisible μ)
    (ξ : ℝ)
    (hzero : charFun μ (2 * ξ) = 0) :
    charFun μ ξ = 0 := by
  sorry
