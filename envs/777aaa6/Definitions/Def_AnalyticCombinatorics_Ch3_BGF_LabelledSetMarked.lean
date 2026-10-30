-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch3_BGF_LabelledSetMarked
-- name    : AnalyticCombinatorics_Ch3_BGF_LabelledSetMarked
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T10:32:34.860447+00:00
-- url     : https://prove2.me/theorems/fffbbdbd-c8bc-44f8-8331-8b73c0a475ee
-- title:
--   Decorated set partitions marked by block count
-- statement:
--   The underlying objects are the original decorated partitions of a finite label set. The mark is the number of nonempty blocks. Polynomial sums over partitions weight each block by its component count and one factor of the marker, so the exponent records block count.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch3/BGF/LabelledSetMarked.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSet
import Definitions.Def_AnalyticCombinatorics_Ch3_BGF_Defs
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Ch3 -- Bivariate EGF transfer theorem for marked labelled sets

For a labelled class `C`, `setMarked C` is `SET(C)` with the number of blocks
marked by the parameter variable `u`. Its bivariate EGF is

  `F(z,u) = exp(u C(z))`,

represented here as substitution into `PowerSeries.exp ℚ[X]`.
-/

open scoped Polynomial

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

/-- `SET(C)` with the number of labelled blocks marked by the parameter variable. -/
noncomputable def ParamClass.setMarked (C : CombClass) : ParamClass where
  toCombClass := C.set
  param _ x := x.1.parts.card

/-- Polynomial-weighted SET sum over all partitions of a finite label type. -/
noncomputable def setMarkedWeightFull (C : CombClass)
    (α : Type*) [Fintype α] [DecidableEq α] : ℚ[X] :=
  ∑ P : Finpartition (Finset.univ : Finset α),
    (((∏ B : P.parts, C.counts B.val.card) : ℕ) : ℚ) •
      (Polynomial.X : ℚ[X]) ^ P.parts.card

/-- Polynomial-weighted SET sum over partitions of a finset. -/
noncomputable def setMarkedWeightFinset (C : CombClass) {α : Type*} [DecidableEq α]
    (s : Finset α) : ℚ[X] :=
  ∑ P : Finpartition s,
    (((∏ B : P.parts, C.counts B.val.card) : ℕ) : ℚ) •
      (Polynomial.X : ℚ[X]) ^ P.parts.card

@[simp] lemma setMarkedWeightFinset_univ
    (C : CombClass) (α : Type*) [Fintype α] [DecidableEq α] :
    setMarkedWeightFinset C (Finset.univ : Finset α) = setMarkedWeightFull C α := rfl

end AnalyticCombinatorics.Ch1


