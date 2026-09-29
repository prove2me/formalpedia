-- Prove2me | solution 1 for mme_regional_target_entropy_bounds
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T21:16:30.727356+00:00
-- url     : https://prove2.me/submissions/01c308ba-54bc-435f-a7bb-f5e8f68f9dee

import Definitions.Def_mme_regional_split_entropy_data
import Theorems.Thm_mme_regional_target_marginals
import Theorems.Thm_mme_regional_prescribed_profile_card
import Theorems.Thm_mme_regional_dependent_profile_entropy_bounds
import Mathlib
open BigOperators MME.RecursiveThinSplit MME.RecursiveXHash MME.RegionRate
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem solution {half R : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) (i : Fin 3)
    (a : Address half R parent n) (ha : a ∈ target m) :
    ((target (n := n) m).card : ℝ) ≤ Real.exp (jointPotential m) ∧
    Real.exp (jointPotential m) ≤
      (6 * (((∑ r, n r : ℕ) : ℝ) + 1)) ^ Fintype.card (MME.RecursiveYZ.Cell half R parent) *
        (target (n := n) m).card ∧
    (((target (n := n) m).image (block i)).card : ℝ) ≤ Real.exp (coarsePotential m i) ∧
    Real.exp (coarsePotential m i) ≤
      (6 * (((∑ r, n r : ℕ) : ℝ) + 1)) ^ (R * (half + 1)) *
        ((target (n := n) m).image (block i)).card := by
  classical
  have hm := mme_regional_target_marginals m i a ha
  have hcard : (target (n := n) m).card = ∏ r, (n r).factorial / ∏ c, (m r c).factorial := by
    have h := mme_regional_prescribed_profile_card n m hm.1
    simp only [Fintype.card_subtype] at h
    convert h using 1
    apply congrArg Finset.card
    ext w
    simp only [target,HasJointCounts,Finset.mem_filter,Finset.mem_univ,true_and]
    apply forall_congr' fun r ↦ forall_congr' fun c ↦ ?_
    unfold count
    apply iff_of_eq
    congr 2
    ext t
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  have hmode : ((target (n := n) m).image (block i)).card =
      ∏ r, (n r).factorial / ∏ j, (marginalCounts m i r j).factorial := by
    rw [hm.2.2]
    have h := mme_regional_prescribed_profile_card n (marginalCounts m i) hm.2.1
    simp only [Fintype.card_subtype] at h
    convert h using 1
    apply congrArg Finset.card
    ext w
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    apply forall_congr' fun r ↦ forall_congr' fun c ↦ ?_
    unfold count
    apply iff_of_eq
    congr 2
    ext t
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  have hnr r : n r ≤ ∑ r, n r :=
    Finset.single_le_sum (f := n) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ r)
  have hj := mme_regional_dependent_profile_entropy_bounds m (∑ r, n r)
    (fun r ↦ (hm.1 r).le.trans (hnr r))
  have hb := mme_regional_dependent_profile_entropy_bounds (marginalCounts m i) (∑ r, n r)
    (fun r ↦ (hm.2.1 r).le.trans (hnr r))
  simp only [hm.1,← Nat.cast_prod,← hcard,jointPotential,coarsePotential,MME.RecursiveYZ.Cell,Fintype.card_sigma] at hj ⊢
  simp only [hm.2.1,← Nat.cast_prod,← hmode,coarsePotential,Fintype.card_fin,
    Finset.sum_const,Finset.card_univ,smul_eq_mul] at hb
  exact ⟨hj.1,hj.2,hb.1,hb.2⟩
