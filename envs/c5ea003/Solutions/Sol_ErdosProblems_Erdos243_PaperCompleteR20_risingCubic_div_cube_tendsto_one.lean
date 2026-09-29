-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.risingCubic_div_cube_tendsto_one
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T22:52:34.902765+00:00
-- url     : https://prove2.me/submissions/78b9ff07-29c7-4c95-8c02-3bceeaa95fa5

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDefect
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateNormalisation
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
end ErdosProblems.Erdos243.PaperCompleteR20

open Filter
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR20 in
theorem solution :
    Tendsto (fun n : ℕ => risingCubic n / (n : ℝ) ^ 3) atTop (nhds 1) := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hprod : Tendsto
      (fun n : ℕ => (1 + ((n : ℝ))⁻¹) * (1 + 2 * ((n : ℝ))⁻¹))
      atTop (nhds 1) := by
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) :=
      tendsto_const_nhds
    simpa using (hone.add hinv).mul (hone.add (htwo.mul hinv))
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  simp only [risingCubic]
  push_cast
  field_simp [hn.ne']
