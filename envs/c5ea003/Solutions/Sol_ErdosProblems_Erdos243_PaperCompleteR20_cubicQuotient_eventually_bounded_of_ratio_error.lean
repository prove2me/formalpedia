-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.cubicQuotient_eventually_bounded_of_ratio_error
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:46:43.788049+00:00
-- url     : https://prove2.me/submissions/51ca909a-0176-4b61-81db-74bd56de1dc9

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateFiniteDifference
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDifferenceLimits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateResidualStep
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateDefect
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientIncrement
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR20_CubicRateQuotientBounded
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR20_cubicQuotient_increment_eq
import Mathlib
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Erdős 243: boundedness of the cubic quotient

The literal `o(n⁻³)` relative error is summable.  Iterating the exact quotient
recurrence therefore expresses the quotient as a fixed initial value times a
convergent infinite-product prefix, which is eventually bounded.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20
open Filter Finset



theorem cubicQuotient_succ_eq_mul_relativeError
    (C : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (hC : C n ≠ 0) :
    cubicQuotient C (n + 1) =
      cubicQuotient C n * (1 + cubicRelativeError C n) := by
  rw [show cubicQuotient C (n + 1) =
      cubicQuotient C n +
        cubicQuotient C n * cubicRatioError C n / (1 + 3 / (n : ℝ)) by
    linarith [cubicQuotient_increment_eq C n hn hC]]
  simp only [cubicRelativeError]
  ring

theorem summable_cubicRatioError_of_scaled_tendsto_zero
    (C : ℕ → ℝ)
    (hratio : Tendsto
      (fun n : ℕ => (n : ℝ) ^ 3 * cubicRatioError C n) atTop (nhds 0)) :
    Summable (cubicRatioError C) := by
  have hone : ∀ᶠ n : ℕ in atTop,
      |(n : ℝ) ^ 3 * cubicRatioError C n| ≤ 1 := by
    exact ((tendsto_order.1 hratio.abs).2 1 (by norm_num)).mono
      (fun _ hn => le_of_lt hn)
  have hbound : ∀ᶠ n : ℕ in atTop,
      ‖cubicRatioError C n‖ ≤ 1 / (n : ℝ) ^ 3 := by
    filter_upwards [hone, eventually_gt_atTop (0 : ℕ)] with n hn hn0
    have hn0r : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [Real.norm_eq_abs]
    calc
      |cubicRatioError C n| =
          |(n : ℝ) ^ 3 * cubicRatioError C n| / (n : ℝ) ^ 3 := by
            rw [abs_mul, abs_of_pos (pow_pos hn0r 3)]
            field_simp
      _ ≤ 1 / (n : ℝ) ^ 3 :=
        div_le_div_of_nonneg_right hn (pow_nonneg hn0r.le 3)
  exact Summable.of_norm_bounded_eventually_nat
    (Real.summable_one_div_nat_pow.mpr (by omega : 1 < 3)) hbound

theorem summable_cubicRelativeError_of_scaled_tendsto_zero
    (C : ℕ → ℝ)
    (hratio : Tendsto
      (fun n : ℕ => (n : ℝ) ^ 3 * cubicRatioError C n) atTop (nhds 0)) :
    Summable (cubicRelativeError C) := by
  have hs := summable_cubicRatioError_of_scaled_tendsto_zero C hratio
  exact hs.norm.of_norm_bounded fun n : ℕ => by
    have hden : (1 : ℝ) ≤ 1 + 3 / (n : ℝ) := le_add_of_nonneg_right (by positivity)
    simp only [cubicRelativeError, norm_div, Real.norm_eq_abs,
      abs_of_nonneg (zero_le_one.trans hden)]
    exact div_le_self (abs_nonneg _) hden
end ErdosProblems.Erdos243.PaperCompleteR20

open Filter Finset
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR20 in
theorem solution
    (C : ℕ → ℝ)
    (hC : ∀ᶠ n in atTop, C n ≠ 0)
    (hratio : Tendsto
      (fun n : ℕ => (n : ℝ) ^ 3 * cubicRatioError C n) atTop (nhds 0)) :
    ∃ M : ℝ, ∀ᶠ n in atTop, |cubicQuotient C n| ≤ M := by
  have hrel := summable_cubicRelativeError_of_scaled_tendsto_zero C hratio
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (hC.and (eventually_gt_atTop (0 : ℕ)))
  have hiter : ∀ k : ℕ,
      cubicQuotient C (N + k) = cubicQuotient C N *
        ∏ i ∈ range k, (1 + cubicRelativeError C (N + i)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hNk := hN (N + k) (Nat.le_add_right N k)
        rw [show N + (k + 1) = (N + k) + 1 by omega,
          cubicQuotient_succ_eq_mul_relativeError C (N + k) hNk.2 hNk.1,
          ih, Finset.prod_range_succ]
        ring
  have hmulShift : Multipliable (fun k => 1 + cubicRelativeError C (N + k)) := by
    exact Real.multipliable_one_add_of_summable
      (hrel.comp_injective (i := fun k : ℕ => N + k)
        (fun _ _ h => Nat.add_left_cancel h))
  have hprod : Tendsto
      (fun k : ℕ => ∏ i ∈ range k, (1 + cubicRelativeError C (N + i)))
      atTop (nhds (∏' i : ℕ, (1 + cubicRelativeError C (N + i)))) :=
    (hmulShift.hasProd_iff_tendsto_nat).1 hmulShift.hasProd
  have hquotShift : Tendsto (fun k => cubicQuotient C (N + k)) atTop
      (nhds (cubicQuotient C N *
        ∏' i : ℕ, (1 + cubicRelativeError C (N + i)))) := by
    apply (hprod.const_mul (cubicQuotient C N)).congr'
    exact Eventually.of_forall fun k => (hiter k).symm
  rcases hquotShift.abs.isBoundedUnder_le with ⟨M, hM⟩
  obtain ⟨K, hK⟩ := eventually_atTop.1 hM
  refine ⟨M, eventually_atTop.2 ⟨N + K, fun n hn => ?_⟩⟩
  have hnN : N ≤ n := le_trans (Nat.le_add_right N K) hn
  have hk : K ≤ n - N := by omega
  simpa [Nat.add_sub_of_le hnN] using hK (n - N) hk
