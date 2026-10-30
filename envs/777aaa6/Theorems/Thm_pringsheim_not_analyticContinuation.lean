-- Prove2me | Theorems.Thm_pringsheim_not_analyticContinuation
-- name    : pringsheim_not_analyticContinuation
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-27T04:34:25.322419+00:00
-- url     : https://prove2.me/theorems/c3c7afd5-c3d6-4ccc-908f-a5d70ccb7a31
-- title:
--   A positive finite radius obstructs analytic continuation
-- statement:
--   Let $a_n\ge0$ and let the scalar complex power series $\sum a_nz^n$ have radius exactly a finite nonnegative real $R>0$. Its sum has no analytic germ $g$ at the positive real point $R$ which agrees with that sum eventually within the open radius-$R$ disk. This is the literal local continuation obstruction at $R$, not a statement about every boundary point.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch4/Analytic/Pringsheim.lean#L252. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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

theorem pringsheim_not_analyticContinuation
    (a : ℕ → ℝ≥0) {R : ℝ≥0} (hRpos : 0 < R)
    (hR :
      (FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).radius =
        (R : ℝ≥0∞)) :
    ¬ ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g (((R : ℝ) : ℂ)) ∧
      g =ᶠ[𝓝[Metric.eball (0 : ℂ) (R : ℝ≥0∞)] (((R : ℝ) : ℂ))]
        (FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))).sum := by sorry
