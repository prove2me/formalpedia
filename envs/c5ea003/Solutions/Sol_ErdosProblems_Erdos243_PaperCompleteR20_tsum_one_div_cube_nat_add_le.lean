-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.tsum_one_div_cube_nat_add_le
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:11:06.132838+00:00
-- url     : https://prove2.me/submissions/75529a35-341f-4d83-98fa-6cda97329456

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDefect
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientIncrement
import Mathlib
import Mathlib.Analysis.PSeries

/-!
# Erdős 243: summing a cubic-rate increment

An increment which is `o(n⁻³)` has a convergent primitive whose tail is
`o(n⁻²)`.  This is the quantitative summation step needed for the literal
ratio error in the paper.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20
open Filter Finset
end ErdosProblems.Erdos243.PaperCompleteR20

open Filter Finset
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR20 in
theorem solution (n : ℕ) (hn : 2 ≤ n) :
    (∑' k : ℕ, 1 / ((n + k : ℕ) : ℝ) ^ 3) ≤ 1 / (n : ℝ) ^ 2 := by
  let u : ℕ → ℝ := fun k => 1 / ((n + k : ℕ) : ℝ) ^ 2
  have hu_nonneg : ∀ k, 0 ≤ u k - u (k + 1) := by
    intro k
    dsimp [u]
    have hpos : (0 : ℝ) < ((n + k : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < n + k by omega)
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le (sq_pos_of_pos hpos)
    gcongr <;> norm_num
  have hu_zero : Tendsto u atTop (nhds 0) := by
    have hbase : Tendsto (fun k : ℕ => (((n + k : ℕ) : ℝ))⁻¹) atTop (nhds 0) :=
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).comp
        (by simpa [Nat.add_comm] using tendsto_add_atTop_nat n)
    simpa [u, one_div, inv_pow] using hbase.pow 2
  have htel : HasSum (fun k => u k - u (k + 1)) (1 / (n : ℝ) ^ 2) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg hu_nonneg]
    have hlim : Tendsto (fun N => u 0 - u N) atTop (nhds (u 0)) := by
      simpa using tendsto_const_nhds.sub hu_zero
    simpa only [Finset.sum_range_sub', u, Nat.add_zero] using hlim
  have hcub : Summable (fun k : ℕ => 1 / ((n + k : ℕ) : ℝ) ^ 3) := by
    exact (Real.summable_one_div_nat_pow.mpr (by omega : 1 < 3)).comp_injective
      (i := fun k : ℕ => n + k) (fun _ _ h => Nat.add_left_cancel h)
  rw [← htel.tsum_eq]
  refine Summable.tsum_le_tsum (fun k => ?_) hcub htel.summable
  dsimp [u]
  push_cast
  have ha : (2 : ℝ) ≤ n + k := by exact_mod_cast le_trans hn (Nat.le_add_right n k)
  have ha0 : (0 : ℝ) < n + k := lt_of_lt_of_le (by norm_num) ha
  have ha1 : (0 : ℝ) < n + (k + 1) := by positivity
  field_simp
  nlinarith [sq_nonneg ((n + k : ℝ) - 1)]
