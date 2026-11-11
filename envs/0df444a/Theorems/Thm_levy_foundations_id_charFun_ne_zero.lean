-- Prove2me | Theorems.Thm_levy_foundations_id_charFun_ne_zero
-- name    : levy_foundations_id_charFun_ne_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T07:51:59.597922+00:00
-- url     : https://prove2.me/theorems/b05e1333-a907-406a-ba6d-98157551d461
-- title:
--   Nonvanishing characteristic function of an infinitely divisible real law
-- statement:
--   The characteristic function of an infinitely divisible probability measure on the real line is nowhere zero. The substantive argument uses convolution roots of every positive order and their infinitesimal triangular-array behaviour.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isInfinitelyDivisible

open MeasureTheory ProbabilityTheory

theorem levy_foundations_id_charFun_ne_zero
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : LevyFoundations.isInfinitelyDivisible μ) :
    ∀ ξ : ℝ, charFun μ ξ ≠ 0 := by
  sorry
