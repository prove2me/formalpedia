-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.muNum_two_term
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T19:09:39.503511+00:00
-- url     : https://prove2.me/submissions/b3b869eb-57a1-4255-85e7-48b914bb99b8

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MuNumModel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MuTilde
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateApprox2
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_assembly_abs_add_three_le
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_erdosWeight_nonneg_of_lt
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_main_kernel_error_rhoModel_le
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_main_model_rho_error_le
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_main_second_order_cross_le
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_model_rhoDropModel_tail_le
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_model_rhoDropModel_tsum_split
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_model_sum_two_term_asymp
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_muNum_far_tail_le
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_muNum_split_main_tail
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_rhoDrop_nonneg
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_summable_model_rhoDropModel_tail
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

open Filter
open scoped BigOperators Topology

noncomputable section

lemma erdosWeight_nonneg_of_mem {n m : ℕ} (hm : m ∈ Finset.Icc 1 (n - 1)) :
    0 ≤ erdosWeight n m := by
  have hmI := Finset.mem_Icc.mp hm
  exact erdosWeight_nonneg_of_lt (n := n) (m := m) (by omega)

end
end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

/-!
# Assembly of the two-term expansion for `muNum`

This file only assembles the banked estimates:

* the infinite model two-term expansion,
* the two main-range errors,
* the weighted Erdős far tail,
* and a local model-product tail.
-/

noncomputable section

open Filter Finset
open scoped Topology BigOperators

end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
open Filter Finset
open scoped Topology BigOperators
theorem solution :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      |muNum n - (3 / massLam + (3 / (2 * massLam ^ 2)) / Real.sqrt (n : ℝ))|
      ≤ K / (n : ℝ) := by
  obtain ⟨Kmodel, hKmodelpos, hKmodel⟩ := model_sum_two_term_asymp
  obtain ⟨Kmain, hKmainpos, hKmain⟩ := main_kernel_error_rhoModel_le
  obtain ⟨Krho, hKrhopos, hKrho⟩ := main_model_rho_error_le
  obtain ⟨Kcross, hKcrosspos, hKcross⟩ := main_second_order_cross_le
  obtain ⟨Ktail, hKtailpos, hKtail⟩ := muNum_far_tail_le
  obtain ⟨Kmtail, hKmtailpos, hKmtail⟩ := model_rhoDropModel_tail_le
  refine ⟨Kmodel + Kmain + Krho + Kcross + Ktail + Kmtail, by linarith, ?_⟩
  filter_upwards [hKmodel, hKmain, hKrho, hKcross, hKtail, hKmtail,
    Filter.eventually_ge_atTop 8] with n hmodel hmain hrho hcross htail hmtail hn8
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  set M : ℕ := ⌊(n : ℝ) ^ (2 / 3 : ℝ)⌋₊ with hMdef
  have hMlt : M < n := by
    have h1 : (M : ℝ) ≤ (n : ℝ) ^ (2 / 3 : ℝ) := by
      rw [hMdef]
      exact Nat.floor_le (Real.rpow_nonneg hnpos.le _)
    have h2 : (n : ℝ) ^ (2 / 3 : ℝ) < (n : ℝ) := by
      calc
        (n : ℝ) ^ (2 / 3 : ℝ) < (n : ℝ) ^ (1 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast (by omega : 1 < n)) (by norm_num)
        _ = (n : ℝ) := Real.rpow_one _
    have : (M : ℝ) < (n : ℝ) := by linarith
    exact_mod_cast this
  have hMle : M ≤ n - 1 := by omega
  set modelT : ℝ :=
    ∑' m : ℕ, if m = 0 then (0 : ℝ) else modelSummand n m * rhoDropModel n m
    with hmodelTdef
  set modelTail : ℝ :=
    ∑' m : ℕ,
      if m ≤ M then (0 : ℝ)
      else if m = 0 then (0 : ℝ) else modelSummand n m * rhoDropModel n m
    with hmodelTaildef
  set mainE : ℝ := ∑ m ∈ Finset.Icc 1 M, erdosWeight n m * rhoDrop n m with hmainEdef
  set mainM : ℝ := ∑ m ∈ Finset.Icc 1 M, modelSummand n m * rhoDropModel n m with hmainMdef
  set tailE : ℝ :=
    ∑ m ∈ Finset.Icc (M + 1) (n - 1), erdosWeight n m * rhoDrop n m with htailEdef
  set L : ℝ := 3 / massLam + (3 / (2 * massLam ^ 2)) / Real.sqrt (n : ℝ) with hLdef
  have hmuSplit : muNum n = mainE + tailE := by
    rw [hmainEdef, htailEdef]
    exact muNum_split_main_tail n M hMle
  have hmodelSplit : modelT = mainM + modelTail := by
    rw [hmodelTdef, hmainMdef, hmodelTaildef]
    exact model_rhoDropModel_tsum_split n M hn1
  have hmainErr : |mainE - mainM| ≤ (Kmain + Krho + Kcross) / (n : ℝ) := by
    rw [hmainEdef, hmainMdef, ← Finset.sum_sub_distrib]
    calc
      |∑ m ∈ Finset.Icc 1 M,
          (erdosWeight n m * rhoDrop n m - modelSummand n m * rhoDropModel n m)|
          ≤ ∑ m ∈ Finset.Icc 1 M,
              |erdosWeight n m * rhoDrop n m - modelSummand n m * rhoDropModel n m| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ m ∈ Finset.Icc 1 M,
            (|erdosWeight n m - modelSummand n m| * |rhoDropModel n m|
              + |modelSummand n m| * |rhoDrop n m - rhoDropModel n m|
              + |erdosWeight n m - modelSummand n m| * |rhoDrop n m - rhoDropModel n m|) := by
            refine Finset.sum_le_sum ?_
            intro m hm
            have hrewrite :
                erdosWeight n m * rhoDrop n m - modelSummand n m * rhoDropModel n m
                  = (erdosWeight n m - modelSummand n m) * rhoDropModel n m
                    + modelSummand n m * (rhoDrop n m - rhoDropModel n m)
                    + (erdosWeight n m - modelSummand n m) *
                        (rhoDrop n m - rhoDropModel n m) := by
              ring
            rw [hrewrite]
            calc
              |(erdosWeight n m - modelSummand n m) * rhoDropModel n m
                    + modelSummand n m * (rhoDrop n m - rhoDropModel n m)
                    + (erdosWeight n m - modelSummand n m) *
                        (rhoDrop n m - rhoDropModel n m)|
                  ≤ |(erdosWeight n m - modelSummand n m) * rhoDropModel n m|
                    + |modelSummand n m * (rhoDrop n m - rhoDropModel n m)|
                    + |(erdosWeight n m - modelSummand n m) *
                        (rhoDrop n m - rhoDropModel n m)| :=
                      assembly_abs_add_three_le _ _ _
              _ =
                |erdosWeight n m - modelSummand n m| * |rhoDropModel n m|
                  + |modelSummand n m| * |rhoDrop n m - rhoDropModel n m|
                  + |erdosWeight n m - modelSummand n m| *
                      |rhoDrop n m - rhoDropModel n m| := by
                    rw [abs_mul, abs_mul, abs_mul]
      _ = (∑ m ∈ Finset.Icc 1 M,
            |erdosWeight n m - modelSummand n m| * |rhoDropModel n m|)
          + (∑ m ∈ Finset.Icc 1 M,
            |modelSummand n m| * |rhoDrop n m - rhoDropModel n m|)
          + (∑ m ∈ Finset.Icc 1 M,
            |erdosWeight n m - modelSummand n m| * |rhoDrop n m - rhoDropModel n m|) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ ≤ Kmain / (n : ℝ) + Krho / (n : ℝ) + Kcross / (n : ℝ) := by
            rw [hMdef]
            linarith [hmain, hrho, hcross]
      _ = (Kmain + Krho + Kcross) / (n : ℝ) := by ring
  have htailEnn : 0 ≤ tailE := by
    rw [htailEdef]
    refine Finset.sum_nonneg ?_
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hmI : m ∈ Finset.Icc 1 (n - 1) := by
      rw [Finset.mem_Icc]
      omega
    have hmn : m ≤ n := by omega
    exact mul_nonneg (erdosWeight_nonneg_of_mem hmI) (rhoDrop_nonneg hmn)
  have htailEabs : |tailE| ≤ Ktail / (n : ℝ) := by
    rw [abs_of_nonneg htailEnn, htailEdef, hMdef]
    exact htail
  have htailSumm := summable_model_rhoDropModel_tail (n := n) (M := M) hn1
  have hmodelTailAbs : |modelTail| ≤ Kmtail / (n : ℝ) := by
    rw [hmodelTaildef]
    have hnorm_eq :
        (∑' i : ℕ, ‖if i ≤ M then (0 : ℝ)
          else if i = 0 then (0 : ℝ) else modelSummand n i * rhoDropModel n i‖)
        =
        (∑' m : ℕ, if m ≤ M then (0 : ℝ)
          else |modelSummand n m * rhoDropModel n m|) := by
      refine tsum_congr ?_
      intro m
      by_cases hm : m ≤ M
      · simp [hm]
      · have hm0 : m ≠ 0 := by omega
        simp [hm, hm0, Real.norm_eq_abs]
    calc
      |∑' m : ℕ,
          if m ≤ M then (0 : ℝ)
          else if m = 0 then (0 : ℝ) else modelSummand n m * rhoDropModel n m|
          = ‖∑' m : ℕ,
              if m ≤ M then (0 : ℝ)
              else if m = 0 then (0 : ℝ) else modelSummand n m * rhoDropModel n m‖ := by
                rw [Real.norm_eq_abs]
      _ ≤ ∑' i : ℕ, ‖if i ≤ M then (0 : ℝ)
          else if i = 0 then (0 : ℝ) else modelSummand n i * rhoDropModel n i‖ :=
            norm_tsum_le_tsum_norm htailSumm.norm
      _ = ∑' m : ℕ, if m ≤ M then (0 : ℝ)
          else |modelSummand n m * rhoDropModel n m| := hnorm_eq
      _ ≤ Kmtail / (n : ℝ) := hmtail
  have hdecomp : muNum n - L = (modelT - L) + (mainE - mainM) + tailE - modelTail := by
    rw [hmuSplit, hmodelSplit]
    ring
  have hmodelAbs : |modelT - L| ≤ Kmodel / (n : ℝ) := by
    rw [hmodelTdef, hLdef]
    exact hmodel
  calc
    |muNum n - (3 / massLam + (3 / (2 * massLam ^ 2)) / Real.sqrt (n : ℝ))|
        = |muNum n - L| := by rw [hLdef]
    _ = |(modelT - L) + (mainE - mainM) + tailE - modelTail| := by rw [hdecomp]
    _ ≤ |(modelT - L) + (mainE - mainM) + tailE| + |modelTail| := by
        rw [sub_eq_add_neg]
        exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
    _ ≤ (|modelT - L| + |mainE - mainM| + |tailE|) + |modelTail| := by
        gcongr
        exact assembly_abs_add_three_le _ _ _
    _ ≤ Kmodel / (n : ℝ) + (Kmain + Krho + Kcross) / (n : ℝ)
          + Ktail / (n : ℝ) + Kmtail / (n : ℝ) := by
        linarith [hmodelAbs, hmainErr, htailEabs, hmodelTailAbs]
    _ = (Kmodel + Kmain + Krho + Kcross + Ktail + Kmtail) / (n : ℝ) := by ring
