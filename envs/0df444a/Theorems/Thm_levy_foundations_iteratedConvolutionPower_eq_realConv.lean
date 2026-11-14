-- Prove2me | Theorems.Thm_levy_foundations_iteratedConvolutionPower_eq_realConv
-- name    : levy_foundations_iteratedConvolutionPower_eq_realConv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T18:26:13.429726+00:00
-- url     : https://prove2.me/theorems/506d5f3a-7808-435a-a48b-fa87fd707cef
-- title:
--   Generic convolution powers agree with the existing real-valued powers
-- statement:
--   When specialised to real measures, the generic recursively defined convolution powers coincide at every natural order with the established Prove2Me real-valued convolution powers.
-- source:
--   Compatibility lemma between Prove2Me's established real-valued levy_foundations_iteratedConv and the new source-faithful generic version of LeanLevy/Levy/InfiniteDivisible.lean; both use the same zero and successor recursion.

import Definitions.Def_levy_foundations_iteratedConvolutionPower
import Definitions.Def_levy_foundations_isInfinitelyDivisibleLaw
import Definitions.Def_levy_foundations_iteratedConv
import Definitions.Def_levy_foundations_isInfinitelyDivisible

open MeasureTheory

theorem levy_foundations_iteratedConvolutionPower_eq_realConv
    (μ : Measure ℝ) (n : ℕ) :
    LevyFoundations.iteratedConvolutionPower μ n =
      LevyFoundations.iteratedConv μ n := by sorry
