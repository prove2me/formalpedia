-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.cubic_size_tendsto_of_normalisedCubicError
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:04:27.522908+00:00
-- url     : https://prove2.me/submissions/0c0baa82-679d-4031-8fe9-0d9f242960f3

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDefect
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateNormalisation
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_risingCubic_div_cube_tendsto_one
import Mathlib

/-!
# Erdős 243: normalised cubic comparison

The remaining product-comparison estimate naturally says that the quotient by
the rising cubic converges to its limit with error `o(n^-2)`.  This file proves
that this single estimate supplies both normalisations required downstream.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20
open Filter





theorem quotient_error_tendsto_zero_of_normalisedCubicError
    (C : ℕ → ℝ) (K : ℝ)
    (herror : Tendsto (normalisedCubicError C K) atTop (nhds 0)) :
    Tendsto (fun n => C n / risingCubic n - K) atTop (nhds 0) := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) atTop (nhds 0) := by
    have hbase : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa [inv_pow] using hbase.pow 2
  have hprod : Tendsto
      (fun n => normalisedCubicError C K n * ((n : ℝ) ^ 2)⁻¹)
      atTop (nhds 0) := by
    simpa using herror.mul hinv
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  simp only [normalisedCubicError]
  field_simp [hn.ne']
end ErdosProblems.Erdos243.PaperCompleteR20

open Filter
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR20 in
theorem solution
    (C : ℕ → ℝ) (K : ℝ)
    (herror : Tendsto (normalisedCubicError C K) atTop (nhds 0)) :
    Tendsto (fun n => C n / (n : ℝ) ^ 3) atTop (nhds K) := by
  have hquot : Tendsto (fun n => C n / risingCubic n) atTop (nhds K) := by
    simpa only [sub_add_cancel, zero_add] using
      (quotient_error_tendsto_zero_of_normalisedCubicError C K herror).add_const K
  have hprod : Tendsto
      (fun n => C n / risingCubic n * (risingCubic n / (n : ℝ) ^ 3))
      atTop (nhds K) := by
    simpa using hquot.mul risingCubic_div_cube_tendsto_one
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  simp only [risingCubic]
  push_cast
  field_simp [hn.ne']
