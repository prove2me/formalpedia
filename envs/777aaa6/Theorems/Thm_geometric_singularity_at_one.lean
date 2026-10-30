-- Prove2me | Theorems.Thm_geometric_singularity_at_one
-- name    : geometric_singularity_at_one
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-27T04:34:25.040093+00:00
-- url     : https://prove2.me/theorems/c5fa7b39-f240-464a-b359-ba1ed4632fe6
-- title:
--   The constant-one power series is singular at one
-- statement:
--   The sum of the source scalar series with every coefficient equal to $1$ is not complex analytic at $z=1$. The sequence is fixed: this is the geometric-series instance of the positive-radius obstruction.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch4/Analytic/PringsheimExample.lean#L17. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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

theorem geometric_singularity_at_one :
    ¬ AnalyticAt ℂ
      (FormalMultilinearSeries.ofScalars ℂ (fun _ : ℕ => (1 : ℂ))).sum
      (1 : ℂ) := by sorry
