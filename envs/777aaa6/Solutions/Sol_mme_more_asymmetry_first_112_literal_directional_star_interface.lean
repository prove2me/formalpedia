-- Prove2me | solution 1 for mme_more_asymmetry_first_112_literal_directional_star_interface
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-06T23:45:26.021227+00:00
-- url     : https://prove2.me/submissions/f3846ce6-03a4-4d7e-b8ef-c134a292e431

import Theorems.Thm_mme_more_asymmetry_first_active_112_profile_source_certificate
import Theorems.Thm_mme_complete_split_112_canonical_profile_router
import Theorems.Thm_mme_complete_split_112_disallowed_word_mismatches_exact_address
import Theorems.Thm_mme_complete_split_112_coupled_basis_label_certificate
import Theorems.Thm_mme_complete_split_112_concrete_four_block_certificate
import Theorems.Thm_mme_primary_hash_family_outerExtractionMap_word_eq_zero_of_mismatch
import Theorems.Thm_mme_primary_hash_family_sharedZ_outer_extraction_exact
import Theorems.Thm_mme_restrict_basisAllAllowedSubtensor_of_vanishes
import Theorems.Thm_mme_primary_hash_family_sharedZ_star_grading_components
import Theorems.Thm_mme_complete_split_112_exact_address_MM_dimensions

open MME MME.CompleteSplit MME.CompleteSplit112 MME.DWZComponentRestriction
open CoupledCTensorPackaging
open scoped NNReal

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem actual_stars_restrict
    {K : Type u} [Field K] (q : ℕ) {N L G A H : ℕ}
    (p : ℚ) (hLG : L + G = N) (hLp : (L : ℚ) = (2 * N : ℕ) * p)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (beta : Fin 3 → Profile 2)
    (hbeta : ∀ mode sigma,
      (beta mode).probability sigma = (profileProbability p mode sigma : ℝ))
    (epsilon : ℝ≥0) :
    TensorObj.Restrict
      (TensorObj.bigAdd (starObj (grading K q) family))
      (restrictedPower (coupledObj K q) (liftedCoordBasis K q)
        (fun mode ↦ fineWord mode ∘ liftedCoordGrade q mode)
        beta epsilon (2 * N)) := by
  classical
  apply mme_restrict_basisAllAllowedSubtensor_of_vanishes
    ((coupledObj K q).kronPow (2 * N))
    (TensorObj.bigAdd (starObj (grading K q) family))
    (fun i ↦ kronPowModeBasis (coupledObj K q) i (liftedCoordBasis K q i) (2 * N))
    (fun i ↦ ApproxConsistent (fineWord i ∘ liftedCoordGrade q i) (beta i) epsilon)
    (outerExtractionMap (grading K q) family)
    (mme_primary_hash_family_sharedZ_outer_extraction_exact
      (grading K q) family
      (mme_complete_split_112_concrete_four_block_certificate (K := K) q).1).1
  intro i w hnot
  have hzero : ∀ (a : Fin 3) (j : LiftedCoord q i),
      liftedCoordGrade q i j ≠ a →
        (grading K q).blockProj i a (liftedCoordBasis K q i j) = 0 := by
    intro a j hne
    exact TensorObj.TypeGrading.blockProj_apply_mem_ne
      (grading K q) i a (liftedCoordGrade q i j) hne.symm
      (liftedCoordBasis K q i j)
      ((mme_complete_split_112_coupled_basis_label_certificate K q).2.2.2 i j)
  exact mme_primary_hash_family_outerExtractionMap_word_eq_zero_of_mismatch
    (grading K q) family i (liftedCoordBasis K q i) (liftedCoordGrade q i) hzero w (by
    intro a h
    exact mme_complete_split_112_disallowed_word_mismatches_exact_address.1
      N L G p hLG hLp i (liftedCoordGrade q i) (beta i)
      (hbeta i) epsilon w hnot (componentExactAddress family a h))

/-- Keep the literal shared-Z star and its actual grading while exposing
each component's three MM dimensions inside the original canonical source. -/
theorem solution :
    ∃ beta : Fin 3 → Profile 2,
      (∀ mode sigma, (beta mode).probability sigma =
        (MoreAsymmetryFirstSlice.probability 0 mode sigma : ℝ)) ∧
      ∀ (K : Type u) [Field K] (m A H : ℕ)
        (family : CWQ6PrimaryHashFamily
          (1180591620717411303424 * m)
          (8959763742786037 * m)
          (1180582660953668517387 * m) A H)
        (epsilon : ℝ≥0),
        TensorObj.Restrict
          (TensorObj.bigAdd (starObj (grading K 5) family))
          (restrictedCanonicalPower K 5 beta epsilon
            (2 * (1180591620717411303424 * m))) ∧
        ∀ a : Fin A,
          (∀ sigma : Fin 3 → Fin (H + 1),
            sigma ∉ Finset.univ.image (cTensorOneHOneAddress H) →
              (starGrading (grading K 5) family a).blockTensor sigma = 0) ∧
          ∀ h : Fin H,
            TensorObj.Isomorphic
              (MMObj K (5 ^ (2 * (1180582660953668517387 * m)))
                (5 ^ (2 * (8959763742786037 * m)))
                (5 ^ (2 * (1180582660953668517387 * m))))
              ((starGrading (grading K 5) family a).blockSubtensor
                (cTensorOneHOneAddress H h)) := by
  obtain ⟨beta, hbeta⟩ :=
    mme_more_asymmetry_first_active_112_profile_source_certificate.{u}.2.2.2.2.2.2.1
  refine ⟨beta 0, hbeta 0, ?_⟩
  intro K inst m A H family epsilon
  have hLG : 8959763742786037 * m + 1180582660953668517387 * m =
      1180591620717411303424 * m := by omega
  have hLp : ((8959763742786037 * m : ℕ) : ℚ) =
      (2 * (1180591620717411303424 * m) : ℕ) * MoreAsymmetryFirstSlice.split0 := by
    norm_num [MoreAsymmetryFirstSlice.split0, Nat.cast_mul]
    ring
  have hprofile : ∀ mode sigma, (beta 0 mode).probability sigma =
      (profileProbability MoreAsymmetryFirstSlice.split0 mode sigma : ℝ) := by
    intro mode sigma
    rw [hbeta 0 mode sigma]
    congr 1
    simp only [MoreAsymmetryFirstSlice.probability, add_zero]
    rfl
  refine ⟨(actual_stars_restrict 5 MoreAsymmetryFirstSlice.split0
    hLG hLp family (beta 0) hprofile epsilon).trans
      (mme_complete_split_112_canonical_profile_router K 5 (beta 0) epsilon
        (2 * (1180591620717411303424 * m))), ?_⟩
  intro a
  have hstar := mme_primary_hash_family_sharedZ_star_grading_components
    (grading K 5) family a
  refine ⟨hstar.1, ?_⟩
  intro h
  exact (mme_complete_split_112_exact_address_MM_dimensions
    (K := K) 5 (1180591620717411303424 * m) (8959763742786037 * m)
    (1180582660953668517387 * m) (componentExactAddress family a h)).trans (hstar.2 h)
