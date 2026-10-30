-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch3_BGF_LabelledSeqMarked
-- name    : AnalyticCombinatorics_Ch3_BGF_LabelledSeqMarked
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T10:32:43.835518+00:00
-- url     : https://prove2.me/theorems/7b7f2744-787b-4b66-9feb-a98605fcde7e
-- title:
--   Factorial-normalized marked series and labelled sequences
-- statement:
--   The bivariate exponential series divides every fixed-size marking polynomial by n!. Labelled sequence objects retain the original label-subset product construction and record their component count, ranging from 0 through the total label size.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch3/BGF/LabelledSeqMarked.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSeq
import Definitions.Def_AnalyticCombinatorics_Ch3_BGF_Defs
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Ch3 -- Bivariate EGF transfer theorem for marked labelled sequences

For a labelled class `C`, `lseqMarked C` is `SEQ(C)` with the number of
components marked by the parameter variable `u`.  Its bivariate EGF satisfies

  `F(z,u) = 1 / (1 - u C(z))`,

represented here as `F * (1 - u C(z)) = 1` over `ℚ[u]⟦z⟧`.
-/

open scoped Polynomial

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

/-- Bivariate exponential generating function, represented as `ℚ[u]⟦z⟧`. -/
noncomputable def ParamClass.begf (C : ParamClass) : ℚ[X]⟦X⟧ :=
  PowerSeries.mk fun n => ((n.factorial : ℚ)⁻¹) • C.paramPoly n

/-- `SEQ(C)` with the number of labelled components marked by the parameter variable. -/
def ParamClass.lseqMarked (C : CombClass) : ParamClass where
  toCombClass := C.lseq
  param _ x := (x.1 : ℕ)

end AnalyticCombinatorics.Ch1


