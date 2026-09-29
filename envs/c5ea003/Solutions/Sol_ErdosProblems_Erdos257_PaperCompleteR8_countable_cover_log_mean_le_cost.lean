-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.countable_cover_log_mean_le_cost
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:00:20.032377+00:00
-- url     : https://prove2.me/submissions/64887d26-ce69-4fee-b100-c9158387e598

import Definitions.Def_ErdosProblems_Erdos257_CoverIndependentPeriodicMean
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_CoverKernel
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_cesaro_le_tsum_divisorMajorantCost
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_divisor_count_le_sum_of_frame_cover
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_exists_finite_frame_subcover
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_finite_subprobability_cover_log_pointwise
import Mathlib
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace ErdosProblems.Erdos257.PaperCompleteR8
end ErdosProblems.Erdos257.PaperCompleteR8

/-!
# Countable positive-cover first logarithmic moment

A finite test support admits a finite subcover. The omitted frame weights
are retained as a subprobability inequality, so no renormalisation cost is
lost. Countable divisor majorants are truncated only at the actual finite
observation horizon; their reciprocal costs are bounded by their convergent
series. The endpoint assumes summability of the explicit total cover cost,
not the logarithmic obstruction it proves.
-/
noncomputable section

namespace ErdosProblems.Erdos257.PaperCompleteR8
open Finset
open ErdosProblems.Erdos257.PaperCompleteR7
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset
open ErdosProblems.Erdos257.PaperCompleteR7
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution
    (F : Finset ℕ) (G : ℕ → Finset ℕ) (η α : ℕ → ℝ) (c : ℕ → ℕ → ℝ)
    (X : ℕ) (hX : 0 < X)
    (hη : HasSum η 1) (hηpos : ∀ j, 0 < η j)
    (hα : ∀ j, 0 < α j ∧ α j ≤ 1)
    (hc : ∀ j d, 0 < d → 0 ≤ c j d)
    (hcolumn : ∀ j, Summable (fun d : ℕ => c j d / (d : ℝ)))
    (hcover : ∀ a ∈ F, ∃ j, a ∈ G j)
    (hmaj : ∀ j n, 0 < n →
      (((G j).filter (fun a => a ∣ n)).card : ℝ) ^ α j ≤ ∑ d ∈ n.divisors, c j d)
    (hcost : Summable (fun j => (∑' d : ℕ, c j d / (d : ℝ)) /
      (η j ^ α j) / ((2 : ℝ) ^ α j - 1))) :
    (∑ n ∈ Finset.Icc 1 X,
      Real.exp 1 * Real.log ((F.filter (fun a => a ∣ n)).card : ℝ)) / X ≤
      ∑' j, (∑' d : ℕ, c j d / (d : ℝ)) /
        (η j ^ α j) / ((2 : ℝ) ^ α j - 1) := by
  classical
  let K : ℕ → ℝ := fun j => (∑' d : ℕ, c j d / (d : ℝ)) /
    (η j ^ α j) / ((2 : ℝ) ^ α j - 1)
  have hden : ∀ j, 0 < (2 : ℝ) ^ α j - 1 := by
    intro j
    have hh := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (hα j).1
    linarith
  have hK : ∀ j, 0 ≤ K j := by
    intro j
    apply div_nonneg _ (hden j).le
    apply div_nonneg _ (Real.rpow_pos_of_pos (hηpos j) _).le
    apply tsum_nonneg
    intro d
    by_cases hd : d = 0
    · simp [hd]
    · exact div_nonneg (hc j d (Nat.pos_of_ne_zero hd)) (Nat.cast_nonneg d)
  by_cases hF : F = ∅
  · simp only [hF, Finset.filter_empty, Finset.card_empty, Nat.cast_zero,
      Real.log_zero, mul_zero, Finset.sum_const_zero, zero_div]
    exact tsum_nonneg hK
  obtain ⟨J, hFJ⟩ := exists_finite_frame_subcover F G hcover
  have hJ : J.Nonempty := by
    obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hF
    obtain ⟨j, hj, _⟩ := Finset.mem_biUnion.mp (hFJ ha)
    exact ⟨j, hj⟩
  have hηJ : ∑ j ∈ J, η j ≤ 1 := by
    have hh := hη.summable.sum_le_tsum J (fun j _ => (hηpos j).le)
    simpa only [hη.tsum_eq] using hh
  have hpoint : ∀ n, Real.exp 1 * Real.log ((F.filter (fun a => a ∣ n)).card : ℝ) ≤
      ∑ j ∈ J, (((G j).filter (fun a => a ∣ n)).card : ℝ) ^ α j /
        (η j ^ α j) / ((2 : ℝ) ^ α j - 1) := by
    intro n
    exact finite_subprobability_cover_log_pointwise J η α _ _ hJ hηJ
      (fun j _ => hηpos j) (fun j _ => hα j)
      (divisor_count_le_sum_of_frame_cover F J G hFJ n)
  calc
    _ ≤ (∑ n ∈ Finset.Icc 1 X, ∑ j ∈ J,
        (((G j).filter (fun a => a ∣ n)).card : ℝ) ^ α j /
          (η j ^ α j) / ((2 : ℝ) ^ α j - 1)) / X :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun n _ => hpoint n)) (Nat.cast_nonneg X)
    _ = ∑ j ∈ J, ((∑ n ∈ Finset.Icc 1 X,
        (((G j).filter (fun a => a ∣ n)).card : ℝ) ^ α j) / X) /
          (η j ^ α j) / ((2 : ℝ) ^ α j - 1) := by
      rw [Finset.sum_comm, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_div, ← Finset.sum_div]
      ring
    _ ≤ ∑ j ∈ J, K j := by
      apply Finset.sum_le_sum
      intro j hj
      have hav := cesaro_le_tsum_divisorMajorantCost
        (fun n => (((G j).filter (fun a => a ∣ n)).card : ℝ) ^ α j)
        (c j) X hX (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (hc j) (hcolumn j) (hmaj j)
      exact div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right hav (Real.rpow_pos_of_pos (hηpos j) _).le) (hden j).le
    _ ≤ _ := hcost.sum_le_tsum J (fun j _ => hK j)
end
