-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch3_BGF_Defs
-- name    : AnalyticCombinatorics_Ch3_BGF_Defs
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T10:32:11.617867+00:00
-- url     : https://prove2.me/theorems/fbb5d9fe-3b9b-4bd8-9c39-64da660e4f0c
-- title:
--   Finite graded objects with natural-valued marks
-- statement:
--   A parameterized class assigns a natural-valued mark to each object of every finite size fibre. Counting objects of size n and mark k gives bivariate counts; summing the powers u^mark gives a finite polynomial for each size. These polynomials form the ordinary size series, with disjoint-sum and Cartesian-product constructions and coefficientwise evaluation of the marker.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch3/BGF/Defs.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Ch3 -- Bivariate generating functions for parameters

This file opens Chapter III with parameterized combinatorial classes.  The BGF
representation is `PowerSeries (Polynomial ℚ)`: the outer power series variable
is size (`z`), while the inner polynomial variable records the parameter (`u`).
For each fixed size the parameter support is finite because the size fiber is
finite.
-/

open scoped Polynomial

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

/-- A combinatorial class equipped with a natural-valued parameter on each
fixed-size fiber. -/
structure ParamClass extends CombClass where
  /-- The parameter value of an object of size `n`. -/
  param : ∀ n, Obj n → ℕ

/-- Bivariate counts: objects of size `n` whose parameter has value `k`. -/
noncomputable def ParamClass.bcounts (C : ParamClass) (n k : ℕ) : ℕ :=
  Fintype.card {x : C.Obj n // C.param n x = k}

/-- The fixed-size parameter polynomial `∑_x u^χ(x)`. -/
noncomputable def ParamClass.paramPoly (C : ParamClass) (n : ℕ) : ℚ[X] :=
  ∑ x : C.Obj n, (Polynomial.X : ℚ[X]) ^ C.param n x

/-- The bivariate generating function, represented as `ℚ[u]⟦z⟧`. -/
noncomputable def ParamClass.bgf (C : ParamClass) : ℚ[X]⟦X⟧ :=
  PowerSeries.mk fun n => C.paramPoly n

/-- Disjoint sum of parameterized classes, preserving the side parameter. -/
def ParamClass.sum (A B : ParamClass) : ParamClass where
  Obj n := A.Obj n ⊕ B.Obj n
  finObj _ := inferInstance
  param n := Sum.elim (A.param n) (B.param n)

/-- Cartesian product of parameterized classes, with additive size and
additive parameter. -/
def ParamClass.prod (A B : ParamClass) : ParamClass where
  Obj n := Σ i : Fin (n + 1), A.Obj i × B.Obj (n - i)
  finObj _ := inferInstance
  param n x := A.param x.1 x.2.1 + B.param (n - x.1) x.2.2

/-- Evaluate the parameter variable `u` while leaving the size variable formal. -/
noncomputable def evalU (a : ℚ) : ℚ[X]⟦X⟧ →+* ℚ⟦X⟧ :=
  PowerSeries.map (Polynomial.evalRingHom a)

end AnalyticCombinatorics.Ch1


