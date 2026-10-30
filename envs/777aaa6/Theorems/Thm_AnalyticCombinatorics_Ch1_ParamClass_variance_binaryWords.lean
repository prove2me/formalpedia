-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch1_ParamClass_variance_binaryWords
-- name    : AnalyticCombinatorics.Ch1.ParamClass.variance_binaryWords
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:25:46.147357+00:00
-- url     : https://prove2.me/theorems/3eaa5612-20b5-44a7-b5e1-5ce74df4e75d
-- title:
--   Variance of the number of ones in binary words
-- statement:
--   Let $\mathcal B_n$ be all functions $\{0,\ldots,n-1\}\to\{\mathrm{false},\mathrm{true}\}$. Write $w(x)$ for the number of true entries and use the uniform counting measure on its $2^n$ elements. For every $n\in\mathbb N$, including zero,
--
--   $$\frac1{2^n}\sum_{x\in\mathcal B_n}w(x)^2-\left(\frac1{2^n}\sum_{x\in\mathcal B_n}w(x)\right)^2=\frac n4.$$
--
--   The identity is in $\mathbb Q$ and uses the source variance operation.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch3/BGF/BinaryWordMoments.lean#L57. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch3_BGF_BinaryWords
import Definitions.Def_AnalyticCombinatorics_Ch3_BGF_Variance
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

theorem AnalyticCombinatorics.Ch1.ParamClass.variance_binaryWords {n : ℕ} :
    ParamClass.binaryWords.variance n = (n : ℚ) / 4 := by sorry
