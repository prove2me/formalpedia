-- Prove2me | Theorems.Thm_levy_foundations_isInfinitelyDivisibleLaw_iff_real
-- name    : levy_foundations_isInfinitelyDivisibleLaw_iff_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T18:26:42.893024+00:00
-- url     : https://prove2.me/theorems/1a4333ac-1aad-4792-9d9b-58aed6ca6190
-- title:
--   Generic and real-valued infinite divisibility agree on real laws
-- statement:
--   A measure on the real line satisfies the new generic infinite-divisibility predicate exactly when it satisfies the existing real-specific Prove2Me predicate. The proof uses compatibility of their iterated convolution powers.
-- source:
--   Compatibility lemma for the two Prove2Me encodings of LeanLevy/Levy/InfiniteDivisible.lean's infinite-divisibility predicate, preserving all positive-order probability roots.

import Definitions.Def_levy_foundations_iteratedConvolutionPower
import Definitions.Def_levy_foundations_isInfinitelyDivisibleLaw
import Definitions.Def_levy_foundations_iteratedConv
import Definitions.Def_levy_foundations_isInfinitelyDivisible

open MeasureTheory

theorem levy_foundations_isInfinitelyDivisibleLaw_iff_real
    (μ : Measure ℝ) :
    LevyFoundations.isInfinitelyDivisibleLaw μ ↔
      LevyFoundations.isInfinitelyDivisible μ := by sorry
