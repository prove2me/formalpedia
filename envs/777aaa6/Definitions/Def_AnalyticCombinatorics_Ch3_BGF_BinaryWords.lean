-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch3_BGF_BinaryWords
-- name    : AnalyticCombinatorics_Ch3_BGF_BinaryWords
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:20:18.276984+00:00
-- url     : https://prove2.me/theorems/3cb28dc0-8581-432c-b748-08efe9b55159
-- title:
--   Binary words with the number of true entries as parameter
-- statement:
--   A size-n object is a function Fin n→Bool. Its parameter is the cardinality of the indices mapped to true. An explicit finite equivalence identifies such a word with its subset of true positions, explaining the binomial parameter polynomial.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch3/BGF/BinaryWords.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch3_BGF_Defs
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
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
# Ch3 -- Binary words marked by number of ones

The class of binary words of length `n`, with the bivariate parameter counting
the number of ones, has BGF `1 / (1 - (1 + u) z)`.
-/

open scoped Polynomial

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

/-- Binary words, with the parameter counting the number of `true` entries. -/
noncomputable def ParamClass.binaryWords : ParamClass where
  Obj n := Fin n → Bool
  finObj _ := inferInstance
  param _ f := (Finset.univ.filter (fun i => f i = true)).card

noncomputable def binaryWordsEquivFinset (n : ℕ) :
    (Fin n → Bool) ≃ Finset (Fin n) where
  toFun f := Finset.univ.filter fun i => f i = true
  invFun s := fun i => decide (i ∈ s)
  left_inv f := by
    funext i
    cases h : f i <;> simp [h]
  right_inv s := by
    ext i
    simp

end AnalyticCombinatorics.Ch1


