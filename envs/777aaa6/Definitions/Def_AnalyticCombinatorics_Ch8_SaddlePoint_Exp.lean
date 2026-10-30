-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Exp
-- name    : AnalyticCombinatorics_Ch8_SaddlePoint_Exp
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T16:12:12.311602+00:00
-- url     : https://prove2.me/theorems/1886606b-c264-4159-8fb8-bcdbaca78b17
-- title:
--   Exponential formal-series coefficients
-- statement:
--   The complex exponential formal series has coefficients1/n!, with a NonnegRealCoeff record providing the real nonnegative representation.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/Exp.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Bound
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
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

def expCarrier : PowerSeries ℂ := PowerSeries.exp ℂ

@[simp] theorem expCarrier_coeff (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n expCarrier = ((1 : ℝ) / n.factorial : ℂ) := by
  simp [expCarrier]

def expCarrier_nonneg : NonnegRealCoeff expCarrier where
  coeffR := fun n => (1 : ℝ) / n.factorial
  coeff_nonneg := by
    intro n
    positivity
  coeff_eq := by
    intro n
    simp


