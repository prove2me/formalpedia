-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Bound
-- name    : AnalyticCombinatorics_Ch8_SaddlePoint_Bound
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T16:08:46.798788+00:00
-- url     : https://prove2.me/theorems/c01725d4-8293-414b-8289-91a98a721093
-- title:
--   Nonnegative real coefficient representations
-- statement:
--   NonnegRealCoeff packages a real nonnegative coefficient sequence with an exact equality to the complex formal-series coefficients. It is a representation with proof fields, not a positivity assumption silently added to all functions.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/Bound.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


open Complex
open scoped NNReal ENNReal

noncomputable section

structure NonnegRealCoeff (F : PowerSeries ℂ) where
  coeffR : ℕ → ℝ
  coeff_nonneg : ∀ n, 0 ≤ coeffR n
  coeff_eq : ∀ n, PowerSeries.coeff (R := ℂ) n F = (coeffR n : ℂ)


