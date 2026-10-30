-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch1_ParamClass_bgf_binaryWords_closed
-- name    : AnalyticCombinatorics.Ch1.ParamClass.bgf_binaryWords_closed
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:25:40.909254+00:00
-- url     : https://prove2.me/theorems/137e92fe-c2ed-45fd-a86d-0b6e2509ab98
-- title:
--   Bivariate generating function of binary words marked by ones
-- statement:
--   Let $\mathcal B_n$ be all functions $\{0,\ldots,n-1\}\to\{\mathrm{false},\mathrm{true}\}$. Write $w(x)$ for the number of true entries and use the uniform counting measure on its $2^n$ elements. Define $B(z,u)=\sum_{n\ge0}(\sum_{x\in\mathcal B_n}u^{w(x)})z^n\in\mathbb Q[u][[z]]$. Then
--
--   $$B(z,u)\bigl(1-(1+u)z\bigr)=1.$$
--
--   The parameter variable is polynomial and the size variable is the outer formal-series variable.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch3/BGF/BinaryWords.lean#L120. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch3_BGF_BinaryWords
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

open AnalyticCombinatorics AnalyticCombinatorics.Ch1

open PowerSeries Finset

theorem AnalyticCombinatorics.Ch1.ParamClass.bgf_binaryWords_closed :
    ParamClass.binaryWords.bgf *
        (1 - PowerSeries.C (1 + Polynomial.X : ℚ[X]) *
          (PowerSeries.X : ℚ[X]⟦X⟧)) =
      1 := by sorry
