-- Prove2me | solution 1 for ErdosProblems.Erdos257.PaperCompleteR8.finite_subprobability_cover_log_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:53:08.4005+00:00
-- url     : https://prove2.me/submissions/a0d3eb4c-f407-40fb-8c25-ef56080b9c5f

import Definitions.Def_ErdosProblems_Erdos257_CoverIndependentPeriodicMean
import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_CoverKernel
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR7_exp_one_mul_log_le_rpow_div
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

/-- A finite fraction of a probability cover still has a sufficiently large frame. -/
theorem exists_frame_ge_subprobability_share (J : Finset ℕ) (η u : ℕ → ℝ) (t : ℝ)
    (hJ : J.Nonempty) (hη : ∑ j ∈ J, η j ≤ 1) (ht : 0 ≤ t)
    (hcover : t ≤ ∑ j ∈ J, u j) :
    ∃ j ∈ J, η j * t ≤ u j := by
  by_contra h
  push_neg at h
  have hs := Finset.sum_lt_sum_of_nonempty hJ h
  have heq : (∑ j ∈ J, η j * t) ≤ t := by
    rw [← Finset.sum_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hη ht
  exact (not_lt_of_ge hcover) (hs.trans_le heq)
end ErdosProblems.Erdos257.PaperCompleteR8

open Finset
open ErdosProblems.Erdos257.PaperCompleteR7
open ErdosProblems in
open ErdosProblems.Erdos257 in
open ErdosProblems.Erdos257.PaperCompleteR8 in
theorem solution (J : Finset ℕ) (η α : ℕ → ℝ)
    (f : ℕ) (g : ℕ → ℕ) (hJ : J.Nonempty)
    (hη : ∑ j ∈ J, η j ≤ 1) (hηpos : ∀ j ∈ J, 0 < η j)
    (hα : ∀ j ∈ J, 0 < α j ∧ α j ≤ 1)
    (hcover : f ≤ ∑ j ∈ J, g j) :
    Real.exp 1 * Real.log (f : ℝ) ≤
      ∑ j ∈ J, (g j : ℝ) ^ α j / (η j ^ α j) / ((2 : ℝ) ^ α j - 1) := by
  have hden : ∀ j ∈ J, 0 < (2 : ℝ) ^ α j - 1 := by
    intro j hj
    have hh := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (hα j hj).1
    linarith
  have hnonneg : ∀ j ∈ J,
      0 ≤ (g j : ℝ) ^ α j / (η j ^ α j) / ((2 : ℝ) ^ α j - 1) := by
    intro j hj
    exact div_nonneg (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.rpow_pos_of_pos (hηpos j hj) _).le) (hden j hj).le
  by_cases hf : f = 0
  · simp only [hf, Nat.cast_zero, Real.log_zero, mul_zero]
    exact Finset.sum_nonneg hnonneg
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hf)
  have hcov : (f : ℝ) ≤ ∑ j ∈ J, (g j : ℝ) := by exact_mod_cast hcover
  obtain ⟨j, hj, hshare⟩ := exists_frame_ge_subprobability_share J η (fun j => (g j : ℝ)) f hJ hη (Nat.cast_nonneg f) hcov
  have hratio : (f : ℝ) ≤ (g j : ℝ) / η j :=
    (le_div_iff₀ (hηpos j hj)).2 (by simpa [mul_comm] using hshare)
  have hp := Real.rpow_le_rpow (Nat.cast_nonneg f) hratio (hα j hj).1.le
  rw [Real.div_rpow (Nat.cast_nonneg _) (hηpos j hj).le (α j)] at hp
  exact (exp_one_mul_log_le_rpow_div hf1 (hα j hj).1 (hα j hj).2).trans
    ((div_le_div_of_nonneg_right hp (hden j hj).le).trans
      (Finset.single_le_sum hnonneg hj))
end
