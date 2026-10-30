-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch7_SingularityApp_FussCatalanNS_fussCatalanGeneral_relative_thirdOrder
-- name    : AnalyticCombinatorics.Ch7.SingularityApp.FussCatalanNS.fussCatalanGeneral_relative_thirdOrder
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-25T18:50:29.912553+00:00
-- url     : https://prove2.me/theorems/e4b0f12c-2b95-47e0-b5fe-3759f2a0dd51
-- title:
--   Relative three-term expansion for fixed-arity Fuss–Catalan coefficients
-- statement:
--   Fix a natural $p\ge2$ and put $q=p-1$. Define
--
--   $$A_p(n)=\frac{\binom{pn}{n}}{qn+1},\qquad \rho_p=\frac{q^q}{p^p},\qquad K_p=\frac{\sqrt p}{q^{3/2}\sqrt{2\pi}},\qquad M_p(n)=K_p\rho_p^{-n}n^{-3/2}.$$
--
--   Set
--
--   $$t_p=-\frac{1+pq}{12pq},\qquad c_1(p)=-\frac{p^2+11p+1}{12pq},\qquad c_2(p)=\frac1{q^2}-\frac{t_p}{q}+\frac{t_p^2}{2}.$$
--
--   Then, as natural $n\to\infty$,
--
--   $$\frac{A_p(n)}{M_p(n)}-\left(1+\frac{c_1(p)}n+\frac{c_2(p)}{n^2}\right)=o(n^{-2}).$$
--
--   The numerator in the selected statement is the real rational binomial expression; a proved source bridge identifies it with the natural Fuss–Catalan sequence. The parameter $p$ stays fixed in the limit. The exact Lean scale is $((n:\mathbb R)^{-1})^2$. No uniformity in $p$, finite-index ratio at $n=0$, fourth-order bound, or independent tree-cardinality interpretation is asserted.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch7/SingularityApp/FussCatalanGeneralThirdOrder.lean#L695. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch7_SingularityApp_FussCatalanGeneralThirdOrder
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
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
/-!
# Third-order Fuss-Catalan coefficient asymptotic, fixed general arity

This file proves the relative third-order asymptotic for the closed form

`1 / ((p - 1)n + 1) * binom (pn) n`.

The only analytic input is the third-order Stirling-sequence expansion already
proved in `CayleyThirdOrder`, applied at `n`, `(p - 1)n`, and `pn`.
-/

set_option maxHeartbeats 1600000

open Filter Asymptotics
open scoped Topology

open AnalyticCombinatorics AnalyticCombinatorics.Ch7 AnalyticCombinatorics.Ch7.SingularityApp AnalyticCombinatorics.Ch7.SingularityApp.FussCatalanNS

theorem AnalyticCombinatorics.Ch7.SingularityApp.FussCatalanNS.fussCatalanGeneral_relative_thirdOrder (p : ℕ) (hp : 2 ≤ p) :
    (fun n : ℕ =>
      fussCatalanRaneyCoeff p n / fussCatalanGeneralMainTerm p n -
        fussCatalanGeneralThirdApprox p n)
      =o[atTop] fun n : ℕ => ((n : ℝ)⁻¹) ^ 2 := by sorry
