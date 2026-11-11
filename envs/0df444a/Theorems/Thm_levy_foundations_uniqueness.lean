-- Prove2me | Theorems.Thm_levy_foundations_uniqueness
-- name    : levy_foundations_uniqueness
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T12:37:17.814757+00:00
-- url     : https://prove2.me/theorems/4ddbf4e2-3430-4f0d-920d-e4bb5828729b
-- title:
--   Existence and uniqueness of the Lévy–Khintchine triple
-- statement:
--   An infinitely divisible probability law determines exactly one drift, nonnegative Gaussian variance and Lévy measure under the stated unit-truncation convention. This is the mission's initial capstone.
-- source:
--   Inspired by Shmuel Link, LeanLevy v0.2.0 (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineUniqueness.lean#L629-L640. Existence and uniqueness of the representing triple. The new Prove2Me theorem requires its own accepted proof and statement audit.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isInfinitelyDivisible
import Definitions.Def_levy_foundations_levyKhintchineTriple
import Definitions.Def_levy_foundations_exponent

open MeasureTheory ProbabilityTheory

theorem levy_foundations_uniqueness
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : LevyFoundations.isInfinitelyDivisible μ) :
    ∃! T : LevyFoundations.LevyKhintchineTriple,
      ∀ ξ : ℝ, charFun μ ξ =
        Complex.exp (LevyFoundations.exponent T ξ) := by
  sorry
