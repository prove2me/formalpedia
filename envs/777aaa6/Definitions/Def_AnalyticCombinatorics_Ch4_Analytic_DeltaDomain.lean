-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_DeltaDomain
-- name    : AnalyticCombinatorics_Ch4_Analytic_DeltaDomain
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T12:40:21.874167+00:00
-- url     : https://prove2.me/theorems/60880856-97e6-4af6-a15f-7874222b7e70
-- title:
--   Indented complex domains around a unit singularity
-- statement:
--   For arbitrary real parameters R and phi, DeltaDomainArg R phi consists of points z with |z|<R, z≠1, and |arg(z-1)|>phi. DeltaDomainGeom R phi consists of points with |z|<R and Re(z-1)<cos(phi)|z-1|. The explicit exclusion z≠1 is retained even for parameters outside the hypotheses of the separate equivalence theorem.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch4/Analytic/DeltaDomain.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


open Complex Filter
open scoped Topology

/--
A Δ-domain is the central object of Flajolet--Sedgewick Chapter VI singularity
analysis. This file provides the geometric scaffolding and standard-function
analyticity used by the general transfer theorem (`transfer_theorem` in
`TransferGeneral.lean`), which derives the `(1 - z)^{-α}` coefficient asymptotics
from a Δ-analytic singular expansion via a little-o Darboux estimate.
-/
def DeltaDomainArg (R φ : ℝ) : Set ℂ :=
  { z | ‖z‖ < R ∧ z ≠ 1 ∧ φ < |Complex.arg (z - 1)| }

def DeltaDomainGeom (R φ : ℝ) : Set ℂ :=
  Metric.ball 0 R ∩ { z | (z - 1).re < Real.cos φ * ‖z - 1‖ }


