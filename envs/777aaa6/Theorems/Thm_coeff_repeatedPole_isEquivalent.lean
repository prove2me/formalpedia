-- Prove2me | Theorems.Thm_coeff_repeatedPole_isEquivalent
-- name    : coeff_repeatedPole_isEquivalent
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T13:35:21.523996+00:00
-- url     : https://prove2.me/theorems/63138dd3-c30d-4e19-aaeb-76f7a0d2bcc5
-- title:
--   Coefficient asymptotics of a repeated formal pole
-- statement:
--   Let $c,a\in\mathbb{C}$ be nonzero and let $d\in\mathbb{N}$. Write $f_n$ for the coefficient of $z^n$ in the formal power series $c(1-az)^{-(d+1)}$. Then, as $n\to\infty$,
--
--   $$f_n\sim c a^n\frac{n^d}{d!}.$$
--
--   This gives the leading coefficient asymptotic for a single pole of order $d+1$, including the geometric case $d=0$. Both nonzero hypotheses are retained.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch4/Analytic/RepeatedPole.lean#L33. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Filter Asymptotics
open scoped PowerSeries Topology BigOperators

open PowerSeries

theorem coeff_repeatedPole_isEquivalent (c a₀ : ℂ) (_ha₀ : a₀ ≠ 0) (_hc : c ≠ 0)
    (d : ℕ) :
    (fun n : ℕ => PowerSeries.coeff (R := ℂ) n
      (PowerSeries.C c * PowerSeries.rescale a₀
        (PowerSeries.invOneSubPow ℂ (d + 1)).val))
      ~[atTop]
    (fun n : ℕ => c * a₀^n * ((n : ℂ)^d / (d.factorial : ℂ))) := by sorry
