-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.cubicAdditiveDefect_tendsto_zero_of_ratioError
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:46:42.572322+00:00
-- url     : https://prove2.me/submissions/f40c894f-4e27-4ba0-a41b-1d9d2f78d973

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDefect
import Mathlib

/-!
# Erdős 243: from ratio little-o to additive cubic defect

The paper states the rate multiplicatively.  This file records the exact
rescaling that converts its `o(n^-3)` error into an additive error tending to
zero once the numerator has cubic size.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20
open Filter



theorem cubicAdditiveDefect_eq_mul_ratioError
    (C : ℕ → ℝ) (n : ℕ) (hC : C n ≠ 0) :
    cubicAdditiveDefect C n = C n * cubicRatioError C n := by
  simp only [cubicAdditiveDefect, cubicRatioError]
  field_simp [hC]

theorem cubicAdditiveDefect_eq_scaled_ratioError
    (C : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (hC : C n ≠ 0) :
    cubicAdditiveDefect C n =
      (C n / (n : ℝ) ^ 3) * ((n : ℝ) ^ 3 * cubicRatioError C n) := by
  rw [cubicAdditiveDefect_eq_mul_ratioError C n hC]
  field_simp [hn.ne']
end ErdosProblems.Erdos243.PaperCompleteR20

open Filter
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR20 in
theorem solution
    (C : ℕ → ℝ) (K : ℝ)
    (hC : ∀ᶠ n in atTop, C n ≠ 0)
    (hcubic : Tendsto (fun n => C n / (n : ℝ) ^ 3) atTop (nhds K))
    (hratio : Tendsto
      (fun n : ℕ => (n : ℝ) ^ 3 * cubicRatioError C n) atTop (nhds 0)) :
    Tendsto (cubicAdditiveDefect C) atTop (nhds 0) := by
  have hprod : Tendsto
      (fun n => (C n / (n : ℝ) ^ 3) *
        ((n : ℝ) ^ 3 * cubicRatioError C n)) atTop (nhds 0) := by
    simpa using hcubic.mul hratio
  apply hprod.congr'
  filter_upwards [hC, eventually_gt_atTop (0 : ℕ)] with n hCn hn
  exact (cubicAdditiveDefect_eq_scaled_ratioError C n hn hCn).symm
