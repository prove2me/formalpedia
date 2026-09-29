-- Prove2me | solution 1 for mme_dwz_q5_fourth_boundary_original_profile_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-21T19:03:51.626078+00:00
-- url     : https://prove2.me/submissions/367f36bb-d25f-4344-ad31-719e9863305f

import Theorems.Thm_mme_dwz_q5_fourth_Zzero_original_profile_endpoints
import Theorems.Thm_mme_dwz_q5_boundary_original_profile_log_floors
import Theorems.Thm_mme_CW_fourth_Xzero_exact_Z_basis_router
import Theorems.Thm_mme_CW_fourth_Yzero_exact_Z_basis_router
import Theorems.Thm_mme_power_basisZAllowedSubtensor_restrict_MM_oneOne_of_exact_router
import Theorems.Thm_mme_power_basisZAllowedSubtensor_restrict_MM_first_of_exact_router
import Theorems.Thm_mme_prescribed_graded_alphabet_word_card
import Theorems.Thm_mme_CW_q5_fourth_Z_grade_fiber_card
import Theorems.Thm_mme_prescribed_Z_six_value_of_graded_MM_word_dimensions
import Mathlib.Tactic
open MME MME.StothersFourth MME.CompleteSplit.CWFourth MME.DWZComponentRestriction
open MME.DWZRestrictedValue MME.CWFourthBoundaryQ5
open scoped BigOperators
universe u
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

private theorem card_eq (k : Fin 9) (p : IntegerZSplitProfile 5)
    (hp : ∀ a, fiberSize k a = 0 → p.count a = 0) (m : ℕ) :
    Nat.card {w : PowIndex (LiftedCoarseCoordinate.{u} 5 k) (p.length m) //
      prescribedZWord (fun a ↦ cwSquarePairGrade 5 a.down.val.1) p m w} =
    Nat.multinomial Finset.univ (fun a ↦ p.count a * m) *
      ∏ a, positiveSize k a ^ (p.count a * m) := by
  classical
  rw [mme_prescribed_graded_alphabet_word_card]
  congr 1
  apply Finset.prod_congr rfl
  intro a _
  have hf := mme_CW_q5_fourth_Z_grade_fiber_card.{u} k a
  rw [hf]
  by_cases hz : fiberSize k a = 0
  · simp [hp a hz]
  · rw [positiveSize, max_eq_right (Nat.one_le_iff_ne_zero.mpr hz)]

private theorem finite_X (K : Type u) [Field K] (j k : Fin 9) (hjk : j.val + k.val = 8)
    (p : IntegerZSplitProfile 5) (hp : ∀ a, fiberSize k a = 0 → p.count a = 0) (m : ℕ) :
    let D := Nat.multinomial Finset.univ (fun a ↦ p.count a * m) *
      ∏ a, positiveSize k a ^ (p.count a * m)
    TensorObj.Restrict (MMObj K 1 1 D)
      (prescribedZPower (cwFourthConstituent K 5 0 j k)
        (constituentBasis K 5 0 j k 2)
        (fun a ↦ cwSquarePairGrade 5 a.down.val.1) p m) := by
  classical
  obtain ⟨coord,maps,ht,hz⟩ := mme_CW_fourth_Xzero_exact_Z_basis_router K 5 j k hjk
  have h := mme_power_basisZAllowedSubtensor_restrict_MM_oneOne_of_exact_router
    (constituentBasis K 5 0 j k 2) (p.length m)
    (prescribedZWord (fun a ↦ cwSquarePairGrade 5 a.down.val.1) p m) coord maps ht hz
  erw [card_eq.{u} k p hp m] at h
  exact h

private theorem finite_Y (K : Type u) [Field K] (j k : Fin 9) (hjk : j.val + k.val = 8)
    (p : IntegerZSplitProfile 5) (hp : ∀ a, fiberSize k a = 0 → p.count a = 0) (m : ℕ) :
    let D := Nat.multinomial Finset.univ (fun a ↦ p.count a * m) *
      ∏ a, positiveSize k a ^ (p.count a * m)
    TensorObj.Restrict (MMObj K D 1 1)
      (prescribedZPower (cwFourthConstituent K 5 j 0 k)
        (constituentBasis K 5 j 0 k 2)
        (fun a ↦ cwSquarePairGrade 5 a.down.val.1) p m) := by
  classical
  obtain ⟨coord,maps,ht,hz⟩ := mme_CW_fourth_Yzero_exact_Z_basis_router K 5 j k hjk
  have h := mme_power_basisZAllowedSubtensor_restrict_MM_first_of_exact_router
    (constituentBasis K 5 j 0 k 2) (p.length m)
    (prescribedZWord (fun a ↦ cwSquarePairGrade 5 a.down.val.1) p m) coord maps ht hz
  erw [card_eq.{u} k p hp m] at h
  exact h

private theorem xy_value (K : Type u) [Field K] (j k : Fin 9) (hjk : j.val + k.val = 8)
    (p : IntegerZSplitProfile 5) (hp : ∀ a, fiberSize k a = 0 → p.count a = 0)
    (tau : ℝ) (htau : 0 < tau) :
    HasPrescribedZSixRestrictionValueAtLeast (cwFourthConstituent K 5 0 j k)
      (constituentBasis K 5 0 j k 2) (fun a ↦ cwSquarePairGrade 5 a.down.val.1)
      p tau (Real.exp (tau * logDimension k p)) ∧
    HasPrescribedZSixRestrictionValueAtLeast (cwFourthConstituent K 5 j 0 k)
      (constituentBasis K 5 j 0 k 2) (fun a ↦ cwSquarePairGrade 5 a.down.val.1)
      p tau (Real.exp (tau * logDimension k p)) := by
  constructor
  · apply mme_prescribed_Z_six_value_of_graded_MM_word_dimensions
      _ _ _ p (positiveSize k) (fun a ↦ lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)) tau htau
    intro m
    exact Or.inl (finite_X K j k hjk p hp m)
  · apply mme_prescribed_Z_six_value_of_graded_MM_word_dimensions
      _ _ _ p (positiveSize k) (fun a ↦ lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)) tau htau
    intro m
    exact Or.inr (finite_Y K j k hjk p hp m)

open MME.DWZQ5GlobalLedger MME.DWZQ5ExactData MME.DWZFourthGlobalWitness

private theorem original_support (c : Fin 45)
    (hc : coarseAddress c 0 = 0 ∨ coarseAddress c 1 = 0) :
    ∀ a, fiberSize (coarseAddress c 2) a = 0 → (rawProfile c).count a = 0 := by
  revert hc c
  decide +kernel

private theorem original_sum (c : Fin 45) :
    (coarseAddress c 0).val + (coarseAddress c 1).val + (coarseAddress c 2).val = 8 := by
  revert c
  decide +kernel

private theorem xy_endpoint {K : Type u} [Field K] (c : Fin 45)
    (hc : coarseAddress c 0 = 0 ∨ coarseAddress c 1 = 0) : ComponentEndpoint K c := by
  have hs := original_sum c
  have hprofile := original_support c hc
  have hV : HasPrescribedZSixRestrictionValueAtLeast
      (cwFourthConstituent K 5 (coarseAddress c 0) (coarseAddress c 1) (coarseAddress c 2))
      (constituentBasis K 5 (coarseAddress c 0) (coarseAddress c 1) (coarseAddress c 2) 2)
      (fun a ↦ cwSquarePairGrade 5 a.down.val.1) (rawProfile c) (790643 / 1000000)
      (Real.exp ((790643 / 1000000) * logDimension (coarseAddress c 2) (rawProfile c))) := by
    rcases hc with hx | hy
    · have hjk : (coarseAddress c 1).val + (coarseAddress c 2).val = 8 := by
        have hz := congrArg Fin.val hx
        change (coarseAddress c 0).val = 0 at hz
        omega
      have h := (xy_value K (coarseAddress c 1) (coarseAddress c 2) hjk
        (rawProfile c) hprofile (790643 / 1000000) (by norm_num)).1
      exact hx.symm ▸ h
    · have hjk : (coarseAddress c 0).val + (coarseAddress c 2).val = 8 := by
        have hz := congrArg Fin.val hy
        change (coarseAddress c 1).val = 0 at hz
        omega
      have h := (xy_value K (coarseAddress c 0) (coarseAddress c 2) hjk
        (rawProfile c) hprofile (790643 / 1000000) (by norm_num)).2
      exact hy.symm ▸ h
  have hle := Real.exp_le_exp.mpr (mme_dwz_q5_boundary_original_profile_log_floors c hc)
  refine ⟨(Real.exp_pos _).le, ?_⟩
  intro v hv hlt cutoff
  exact hV.2 v hv (hlt.trans_le hle) cutoff

theorem solution {K : Type u} [Field K]
    (c : Fin 45) (hc : ∃ i : Fin 3, MME.DWZFourthGlobalWitness.coarseAddress c i = 0) :
    MME.DWZQ5GlobalLedger.ComponentEndpoint K c := by
  obtain ⟨i,hi⟩ := hc
  fin_cases i
  · exact xy_endpoint c (Or.inl hi)
  · exact xy_endpoint c (Or.inr hi)
  · exact mme_dwz_q5_fourth_Zzero_original_profile_endpoints c hi
