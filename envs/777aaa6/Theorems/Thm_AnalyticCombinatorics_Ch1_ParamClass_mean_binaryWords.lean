-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch1_ParamClass_mean_binaryWords
-- name    : AnalyticCombinatorics.Ch1.ParamClass.mean_binaryWords
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:25:41.731223+00:00
-- url     : https://prove2.me/theorems/4a3cece4-3bb3-4017-ac43-c67682195686
-- title:
--   Mean number of ones in binary words
-- statement:
--   Let $\mathcal B_n$ be all functions $\{0,\ldots,n-1\}\to\{\mathrm{false},\mathrm{true}\}$. Write $w(x)$ for the number of true entries and use the uniform counting measure on its $2^n$ elements. For $n\ge1$,
--
--   $$\frac1{2^n}\sum_{x\in\mathcal B_n}w(x)=\frac n2.$$
--
--   This is the source rational ParamClass mean. The public theorem retains $n\ge1$ even though the source also contains a private all-size identity.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch3/BGF/BinaryWordMoments.lean#L51. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch3_BGF_BinaryWords
import Definitions.Def_AnalyticCombinatorics_Ch3_BGF_Moments
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
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
# Ch3 -- Mean and variance for ones in binary words

For length-`n` binary words, the number of ones has the binomial distribution
`Bin(n, 1/2)`.
-/

open scoped Polynomial

open AnalyticCombinatorics AnalyticCombinatorics.Ch1

open PowerSeries Finset

theorem AnalyticCombinatorics.Ch1.ParamClass.mean_binaryWords {n : ℕ} (hn : 1 ≤ n) :
    ParamClass.binaryWords.mean n = (n : ℚ) / 2 := by sorry
