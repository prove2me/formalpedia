-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
-- name    : AnalyticCombinatorics_Ch4_Analytic_Bridge
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T12:40:12.738977+00:00
-- url     : https://prove2.me/theorems/39d05458-b33e-4bc6-a30e-8ed1093d9770
-- title:
--   Formal complex series and their analytic sums
-- statement:
--   A complex formal power series determines a scalar formal multilinear series. Its analyticSum is the totalized series sum of that multilinear series, defined for every complex argument; this definition makes no convergence assertion. Rational formal series map coefficientwise into the complex numbers.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch4/Analytic/Bridge.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


open Filter ENNReal
open scoped PowerSeries Topology NNReal ENNReal

noncomputable section

namespace PowerSeries

def toFMLS (f : PowerSeries ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (fun n => PowerSeries.coeff (R := ℂ) n f)

def analyticSum (f : PowerSeries ℂ) (z : ℂ) : ℂ :=
  (toFMLS f).sum z

def mapℂ : PowerSeries ℚ →+* PowerSeries ℂ :=
  PowerSeries.map (algebraMap ℚ ℂ)

end PowerSeries


