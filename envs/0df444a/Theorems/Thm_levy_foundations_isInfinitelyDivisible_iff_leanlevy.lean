-- Prove2me | Theorems.Thm_levy_foundations_isInfinitelyDivisible_iff_leanlevy
-- name    : levy_foundations_isInfinitelyDivisible_iff_leanlevy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T08:05:26.169835+00:00
-- url     : https://prove2.me/theorems/7262c235-07e0-4792-80e4-ba2e4fcaa750
-- title:
--   Equivalence of the Prove2Me and original LeanLevy infinite divisibility definitions
-- statement:
--   For a real measure, the Prove2Me infinite-divisibility predicate is equivalent to the original LeanLevy predicate. Both require every positive-order convolution root to be a probability measure. Their real-valued iterated convolution definitions agree by induction.
-- source:
--   Source-faithful bridge to LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/InfiniteDivisible.lean lines 42–92. Supports levy_foundations_representation milestone M5.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_iteratedConv
import Definitions.Def_levy_foundations_isInfinitelyDivisible
import Definitions.Def_LeanLevy_Levy_InfiniteDivisible

open MeasureTheory ProbabilityTheory

theorem levy_foundations_isInfinitelyDivisible_iff_leanlevy (μ : Measure ℝ) :
    LevyFoundations.isInfinitelyDivisible μ ↔ ProbabilityTheory.IsInfinitelyDivisible μ := by
  sorry
