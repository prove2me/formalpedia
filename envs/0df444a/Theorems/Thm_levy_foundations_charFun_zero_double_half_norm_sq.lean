-- Prove2me | Theorems.Thm_levy_foundations_charFun_zero_double_half_norm_sq
-- name    : levy_foundations_charFun_zero_double_half_norm_sq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T08:01:17.618272+00:00
-- url     : https://prove2.me/theorems/309a6c1f-3034-4525-b27a-01755a0ec741
-- title:
--   Half-frequency modulus bound when a characteristic function vanishes at double frequency
-- statement:
--   For any probability law ν and real ξ, if its characteristic function is zero at 2ξ, then the squared modulus of its characteristic function at ξ is at most one half. This follows from 2|φ(ξ)|² ≤ 1+|φ(2ξ)|, itself a positive-definiteness or complex variance inequality. It is the analytic input to dyadic zero propagation for infinitely divisible laws.

import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

open MeasureTheory ProbabilityTheory

theorem levy_foundations_charFun_zero_double_half_norm_sq
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (ξ : ℝ)
    (hzero : charFun ν (2 * ξ) = 0) :
    ‖charFun ν ξ‖ ^ 2 ≤ (1 / 2 : ℝ) := by
  sorry
