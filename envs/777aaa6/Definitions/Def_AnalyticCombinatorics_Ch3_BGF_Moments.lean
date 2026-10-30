-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch3_BGF_Moments
-- name    : AnalyticCombinatorics_Ch3_BGF_Moments
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T10:32:41.262991+00:00
-- url     : https://prove2.me/theorems/4872c552-64da-4f61-ba06-4fc06ff1c96d
-- title:
--   Marker derivatives and finite first moments
-- statement:
--   Differentiate each fixed-size parameter polynomial in its marker, evaluate at one and normalize by the finite fibre count to obtain the rational mean. Integer compositions are marked by their number of parts. The derivative-series and first factorial-moment operations act on the original formal polynomial-coefficient series. On an empty size fibre the total rational definition gives zero; a uniform-probability interpretation requires a nonempty fibre.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch3/BGF/Moments.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Sequence
import Definitions.Def_AnalyticCombinatorics_Ch3_BGF_Defs
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
# Ch3 -- Moments of bivariate generating functions

The first factorial moment differentiates the parameter variable `u` and then
sets `u = 1`.  For a parameterized class this extracts the cumulative parameter
over each fixed-size fiber.
-/

open scoped Polynomial

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- Formal derivative in the parameter variable `u`, coefficientwise in size. -/
noncomputable def uDeriv (F : ℚ[X]⟦X⟧) : ℚ[X]⟦X⟧ :=
  PowerSeries.mk fun n => Polynomial.derivative (PowerSeries.coeff n F)

/-- First factorial moment series: differentiate in `u`, then set `u = 1`. -/
noncomputable def factorialMoment1 (F : ℚ[X]⟦X⟧) : ℚ⟦X⟧ :=
  evalU 1 (uDeriv F)

/-- Mean value of the parameter on the size-`n` fiber. -/
noncomputable def ParamClass.mean (C : ParamClass) (n : ℕ) : ℚ :=
  PowerSeries.coeff n (factorialMoment1 C.bgf) / (C.toCombClass.counts n : ℚ)

/-- Integer compositions parameterized by their number of parts. -/
def ParamClass.compositionsByParts : ParamClass where
  toCombClass := CombClass.compositions
  param _ c := c.length

end AnalyticCombinatorics.Ch1


