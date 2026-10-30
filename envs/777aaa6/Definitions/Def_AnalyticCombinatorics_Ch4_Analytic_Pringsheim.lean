-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Pringsheim
-- name    : AnalyticCombinatorics_Ch4_Analytic_Pringsheim
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-27T04:33:21.666113+00:00
-- url     : https://prove2.me/theorems/be61d397-e813-4c5f-aae5-85d9458f89b1
-- title:
--   Nonnegative scalar formal series
-- statement:
--   For a sequence a : Nat → NNReal, pringsheimSeries a is the complex formal multilinear series ofScalars with coefficient a n cast to Complex. It packages the nonnegative scalar power series used in the source Pringsheim argument.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch4/Analytic/Pringsheim.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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


open Filter
open scoped NNReal ENNReal Topology

noncomputable section

abbrev pringsheimSeries (a : ℕ → ℝ≥0) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))


