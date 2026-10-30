-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_SecondOrderHAdmissible
-- name    : AnalyticCombinatorics_Ch8_SaddlePoint_SecondOrderHAdmissible
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T16:15:21.714745+00:00
-- url     : https://prove2.me/theorems/99198f05-760d-4ae5-8e64-9624f1dea734
-- title:
--   Second-order local and tail accuracy records
-- statement:
--   The record stores b3,b4 and an eventually positive vanishing correction scale c2. Its proof fields require Q2=O(c2), weighted central L1 accuracy o(c2), and uniform angular tail accuracy at the same scale. These are supplied accuracy data, not automatic consequences of analyticity.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/SecondOrderHAdmissible.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_HAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_SecondOrderCore
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Second-order H-admissible wrapper

This is a clean add-on to the first-order `HAdmissible` interface.  It records
the third and fourth logarithmic saddle derivatives, the robust correction
scale, and the local/tail hypotheses used by the second-order saddle layer.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

/-- Second-order Hayman data over an existing first-order H-admissible instance. -/
structure SecondOrderHAdmissible {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (hf : HAdmissible f p) where
  b3 : ℝ → ℝ
  b4 : ℝ → ℝ
  corrScale : ℝ → ℝ

  corrScale_pos : ∀ᶠ r : ℝ in hf.radFilter, 0 < corrScale r
  corrScale_tendsto_zero : Tendsto corrScale hf.radFilter (𝓝 0)
  corrScale_dominates_correction :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ r : ℝ in hf.radFilter,
        saddleCorrectionScale hf.b b3 b4 r ≤ K * corrScale r

  local_second_L1 :
    Tendsto
      (fun r : ℝ =>
        (∫ x in -(hf.δ r * Real.sqrt (hf.b r))..(hf.δ r * Real.sqrt (hf.b r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio f hf.a hf.b r (x / Real.sqrt (hf.b r)) -
              saddleSecondPoly hf.b b3 b4 r x)‖) / corrScale r)
      hf.radFilter (𝓝 0)

  tail_second_uniform :
    ∃ E : ℝ → ℝ,
      (∀ᶠ r : ℝ in hf.radFilter, 0 ≤ E r) ∧
      Tendsto
        (fun r : ℝ => Real.sqrt (2 * Real.pi * hf.b r) * E r / corrScale r)
        hf.radFilter (𝓝 0) ∧
      (∀ᶠ r : ℝ in hf.radFilter, ∀ n : ℕ, ∀ θ : ℝ,
        hf.δ r ≤ |θ| → |θ| ≤ Real.pi → ‖saddleGAt f r n θ‖ ≤ E r)


