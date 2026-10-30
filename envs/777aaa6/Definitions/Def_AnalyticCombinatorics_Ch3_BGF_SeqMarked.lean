-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch3_BGF_SeqMarked
-- name    : AnalyticCombinatorics_Ch3_BGF_SeqMarked
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T10:32:34.983008+00:00
-- url     : https://prove2.me/theorems/3e26c672-9400-4ca6-b6cc-ddd414430e59
-- title:
--   Ordered sequences marked by component count
-- statement:
--   The underlying finite objects are the original ordered positive-part component sequences, marked by their number of components. Rational coefficient series embed coefficientwise into series of constant polynomials, allowing the marker u to record each component.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch3/BGF/SeqMarked.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Sequence
import Definitions.Def_AnalyticCombinatorics_Ch3_BGF_Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Ch3 -- BGF transfer theorem for marked sequences

For an ordinary class `C`, `seqMarked C` is `SEQ(C)` with the sequence length
marked by the parameter variable `u`.  Its BGF satisfies
`F(z,u) = 1 / (1 - u C(z))`, represented here as
`F * (1 - u C(z)) = 1`.
-/

open scoped Polynomial

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

/-- Coefficientwise embedding from OGFs into BGFs. -/
noncomputable def liftU : ℚ⟦X⟧ →+* ℚ[X]⟦X⟧ :=
  PowerSeries.map (Polynomial.C : ℚ →+* ℚ[X])

/-- `SEQ(C)` with the sequence length marked by the parameter variable. -/
def ParamClass.seqMarked (C : CombClass) : ParamClass where
  toCombClass := C.seq
  param _ x := x.1.length

end AnalyticCombinatorics.Ch1


