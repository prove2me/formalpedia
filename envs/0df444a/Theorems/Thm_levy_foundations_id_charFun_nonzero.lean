-- Prove2me | Theorems.Thm_levy_foundations_id_charFun_nonzero
-- name    : levy_foundations_id_charFun_nonzero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T07:58:49.190149+00:00
-- url     : https://prove2.me/theorems/40c47941-45bc-4fce-ad03-f3e110592afc
-- title:
--   The characteristic function of an infinitely divisible real law never vanishes
-- statement:
--   If a real probability law has convolution roots of every positive integer order, its characteristic function has no zeros. An elementary route uses the root identity, continuity at the origin and a unit-circle moment bound to propagate approximate modulus one from ξ/k to ξ.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isInfinitelyDivisible

open MeasureTheory ProbabilityTheory

/-- Infinite divisibility forces the characteristic function to be nonzero. -/
theorem levy_foundations_id_charFun_nonzero
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : LevyFoundations.isInfinitelyDivisible μ) :
    ∀ ξ : ℝ, charFun μ ξ ≠ 0 := by sorry
