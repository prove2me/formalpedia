-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Poles
-- name    : AnalyticCombinatorics_Ch4_Analytic_Poles
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T12:40:23.742896+00:00
-- url     : https://prove2.me/theorems/4996f7d2-6e37-400b-87ff-458ed36848d6
-- title:
--   Formal simple and double unit poles
-- statement:
--   The complex formal series pole1 is the inverse of 1-X, and pole2 is the square of that inverse, equivalently the inverse of (1-X)².
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch4/Analytic/Poles.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
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
open scoped PowerSeries Topology

noncomputable section

namespace PowerSeries

def pole1 : PowerSeries ℂ := invUnitsSub (1 : ℂˣ)
def pole2 : PowerSeries ℂ := (invOneSubPow ℂ 2).val

end PowerSeries


