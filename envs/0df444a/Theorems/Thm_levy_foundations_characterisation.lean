-- Prove2me | Theorems.Thm_levy_foundations_characterisation
-- name    : levy_foundations_characterisation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T12:37:01.680383+00:00
-- url     : https://prove2.me/theorems/6e069af4-0181-4f1f-b9f4-41f6661ba406
-- title:
--   Characterisation of infinite divisibility by Lévy–Khintchine triples
-- statement:
--   A probability law on ℝ is infinitely divisible if and only if its characteristic function is the exponential of a Lévy–Khintchine exponent.
-- source:
--   Inspired by Shmuel Link, LeanLevy v0.2.0 (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineUniqueness.lean#L607-L624. The bidirectional Lévy–Khintchine theorem. The new Prove2Me theorem requires its own accepted proof and statement audit.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isInfinitelyDivisible
import Definitions.Def_levy_foundations_levyKhintchineTriple
import Definitions.Def_levy_foundations_exponent

open MeasureTheory ProbabilityTheory

theorem levy_foundations_characterisation
    {μ : Measure ℝ} [IsProbabilityMeasure μ] :
    LevyFoundations.isInfinitelyDivisible μ ↔
      ∃ T : LevyFoundations.LevyKhintchineTriple,
        ∀ ξ : ℝ, charFun μ ξ =
          Complex.exp (LevyFoundations.exponent T ξ) := by
  sorry
