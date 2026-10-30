-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch3_BGF_Variance
-- name    : AnalyticCombinatorics_Ch3_BGF_Variance
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T10:33:07.470807+00:00
-- url     : https://prove2.me/theorems/01f27f79-678d-4402-b520-ded14fed3d95
-- title:
--   Finite second moments and rational variance
-- statement:
--   Twice differentiating the marker gives second factorial-moment coefficients. Adding the first moment gives squared-mark sums. Rational variance is the normalized second raw moment minus the square of the finite mean; generic division is totalized, while the selected positive-size composition fibres have nonzero count. On an empty size fibre the total rational definition gives zero; a uniform-probability interpretation requires a nonempty fibre.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch3/BGF/Variance.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch3_BGF_Moments
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Ch3 -- Variance and bivariate composition facts

The second factorial moment differentiates twice in the parameter variable.
Adding the first factorial moment gives the second raw moment, hence the usual
variance formula for any parameterized class.
-/

open scoped Polynomial

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

/-- Second factorial moment series: differentiate twice in `u`, then set
`u = 1`. -/
noncomputable def factorialMoment2 (F : ℚ[X]⟦X⟧) : ℚ⟦X⟧ :=
  evalU 1 (uDeriv (uDeriv F))

/-- Second raw moment series: `E[p(p-1)] + E[p]` before normalization. -/
noncomputable def rawMoment2 (F : ℚ[X]⟦X⟧) : ℚ⟦X⟧ :=
  evalU 1 (uDeriv (uDeriv F) + uDeriv F)

/-- Variance of the parameter on the size-`n` fiber. -/
noncomputable def ParamClass.variance (C : ParamClass) (n : ℕ) : ℚ :=
  PowerSeries.coeff n (rawMoment2 C.bgf) / (C.toCombClass.counts n : ℚ) - C.mean n ^ 2

end AnalyticCombinatorics.Ch1


