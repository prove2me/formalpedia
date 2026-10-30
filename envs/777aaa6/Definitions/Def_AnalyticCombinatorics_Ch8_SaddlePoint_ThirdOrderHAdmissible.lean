-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ThirdOrderHAdmissible
-- name    : AnalyticCombinatorics_Ch8_SaddlePoint_ThirdOrderHAdmissible
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T16:18:49.278741+00:00
-- url     : https://prove2.me/theorems/7b2adbb7-f687-4800-a196-763862338dca
-- title:
--   Higher polynomial local and tail accuracy records
-- statement:
--   The record extends the supplied first and second records with b5,b6 and an eventually positive vanishing scale c3. Proof fields require Q3=O(c3), the explicit P3 weighted local L1 error divided by c3 tending to zero, and a uniform tail bound whose Gaussian-scaled size is o(c3). No field requires c3=o(c2).
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/SaddlePoint/ThirdOrderHAdmissible.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_SecondOrderHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ThirdOrderCore
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
# Third-order H-admissible wrapper

This is a clean add-on to the second-order `HAdmissible` interface.  It records
the fifth and sixth logarithmic saddle derivatives, the robust third-order
scale, and the local/tail hypotheses used by the third-order saddle layer.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

/-- Third-order Hayman data over an existing second-order H-admissible instance. -/
structure ThirdOrderHAdmissible {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (hf : HAdmissible f p)
    (h2 : SecondOrderHAdmissible hf) where
  b5 : ℝ → ℝ
  b6 : ℝ → ℝ
  corrScale3 : ℝ → ℝ

  corrScale3_pos : ∀ᶠ r : ℝ in hf.radFilter, 0 < corrScale3 r
  corrScale3_tendsto_zero : Tendsto corrScale3 hf.radFilter (𝓝 0)
  corrScale3_dominates_correction :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ r : ℝ in hf.radFilter,
        saddleThirdCorrectionScale hf.b h2.b3 h2.b4 b5 b6 r ≤ K * corrScale3 r

  local_third_L1 :
    Tendsto
      (fun r : ℝ =>
        (∫ x in -(hf.δ r * Real.sqrt (hf.b r))..(hf.δ r * Real.sqrt (hf.b r)),
          ‖Complex.exp (-(x ^ 2) / 2) *
            (saddleLocalRatio f hf.a hf.b r (x / Real.sqrt (hf.b r)) -
              saddleThirdPoly hf.b h2.b3 h2.b4 b5 b6 r x)‖) / corrScale3 r)
      hf.radFilter (𝓝 0)

  tail_third_uniform :
    ∃ E : ℝ → ℝ,
      (∀ᶠ r : ℝ in hf.radFilter, 0 ≤ E r) ∧
      Tendsto
        (fun r : ℝ => Real.sqrt (2 * Real.pi * hf.b r) * E r / corrScale3 r)
        hf.radFilter (𝓝 0) ∧
      (∀ᶠ r : ℝ in hf.radFilter, ∀ n : ℕ, ∀ θ : ℝ,
        hf.δ r ≤ |θ| → |θ| ≤ Real.pi → ‖saddleGAt f r n θ‖ ≤ E r)


