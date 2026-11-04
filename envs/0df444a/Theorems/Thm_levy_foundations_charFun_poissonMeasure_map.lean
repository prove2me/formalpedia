-- Prove2me | Theorems.Thm_levy_foundations_charFun_poissonMeasure_map
-- name    : levy_foundations_charFun_poissonMeasure_map
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T18:30:16.21388+00:00
-- url     : https://prove2.me/theorems/6f701da4-1229-4dcc-9008-b51b485e1ead
-- title:
--   Characteristic function of the real-valued Poisson law
-- statement:
--   The real pushforward of a Poisson law has characteristic function exp(r(exp(iξ)-1)).
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Probability/Poisson.lean#L229-L232

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Group.Convolution

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal Nat

theorem levy_foundations_charFun_poissonMeasure_map (r : ℝ≥0) (ξ : ℝ) :
    charFun ((poissonMeasure r).map (Nat.cast : ℕ → ℝ)) ξ =
      cexp (r * (cexp (ξ * I) - 1)) := by sorry
