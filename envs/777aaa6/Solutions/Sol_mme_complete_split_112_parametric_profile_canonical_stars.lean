-- Prove2me | solution 1 for mme_complete_split_112_parametric_profile_canonical_stars
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T00:19:15.710638+00:00
-- url     : https://prove2.me/submissions/b0348805-abc0-4ceb-981d-e1feb7e015da

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
open scoped NNReal BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem probability_nonnegative (p : ℚ) (hp : 0 ≤ p) (hp2 : 2 * p ≤ 1)
    (mode : Fin 3) (word : Fin 2 → Fin 3) :
    0 ≤ profileProbability p mode word := by
  unfold profileProbability
  split_ifs <;> linarith

private theorem probability_sum (p : ℚ) (mode : Fin 3) :
    (∑ word : Fin 2 → Fin 3, profileProbability p mode word) = 1 := by
  rw [← (finTwoArrowEquiv (Fin 3)).symm.sum_comp (profileProbability p mode)]
  fin_cases mode <;>
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ,
      finTwoArrowEquiv, profileProbability]
  ring

private theorem probability_wrong_grade (p : ℚ)
    (mode : Fin 3) (word : Fin 2 → Fin 3)
    (hwrong : (word 0).val + (word 1).val ≠ (cwSquareBlockType 1 1 2 mode).val) :
    profileProbability p mode word = 0 := by
  generalize h0 : word 0 = a
  generalize h1 : word 1 = b
  fin_cases mode <;> fin_cases a <;> fin_cases b <;>
    simp_all [profileProbability, cwSquareBlockType]

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

/-- Every admissible rational112 profile, including the endpoints, gives
literal same-family canonical star extraction at every exactly compatible
power. Support is inclusion only, not an endpoint-false equivalence. -/
theorem solution (p : ℚ) (hp : 0 ≤ p) (hp2 : 2 * p ≤ 1) :
    ∃ beta : Fin 3 → Profile 2,
      (∀ mode sigma, (beta mode).probability sigma =
        (profileProbability p mode sigma : ℝ)) ∧
      (∀ mode sigma,
        (sigma 0).val + (sigma 1).val ≠ (cwSquareBlockType 1 1 2 mode).val →
          (beta mode).probability sigma = 0) ∧
      ∀ (K : Type u) [Field K] (q N L G A H : ℕ)
        (family : CWQ6PrimaryHashFamily N L G A H)
        (_hLG : L + G = N) (_hLp : (L : ℚ) = (2 * N : ℕ) * p)
        (epsilon : ℝ≥0),
        TensorObj.Restrict
          (TensorObj.bigAdd (starObj (grading K q) family))
          (restrictedCanonicalPower K q beta epsilon (2 * N)) ∧
        ∀ a : Fin A,
          (∀ sigma : Fin 3 → Fin (H + 1),
            sigma ∉ Finset.univ.image (cTensorOneHOneAddress H) →
              (starGrading (grading K q) family a).blockTensor sigma = 0) ∧
          ∀ h : Fin H,
            TensorObj.Isomorphic
              (MMObj K (q ^ (2 * G)) (q ^ (2 * L)) (q ^ (2 * G)))
              ((starGrading (grading K q) family a).blockSubtensor
                (cTensorOneHOneAddress H h)) := by
  let beta (mode : Fin 3) : Profile 2 := {
    level_pos := by decide
    probability sigma := (profileProbability p mode sigma : ℝ)
    nonnegative sigma := by
      exact_mod_cast probability_nonnegative p hp hp2 mode sigma
    sum_eq_one := by exact_mod_cast probability_sum p mode }
  refine ⟨beta, (fun _ _ ↦ rfl), ?_, ?_⟩
  · intro mode sigma hwrong
    change (profileProbability p mode sigma : ℝ) = 0
    rw [probability_wrong_grade p mode sigma hwrong, Rat.cast_zero]
  · intro K inst q N L G A H family hLG hLp epsilon
    refine ⟨(actual_stars_restrict q p hLG hLp family beta
      (fun _ _ ↦ rfl) epsilon).trans
        (mme_complete_split_112_canonical_profile_router K q beta epsilon (2 * N)), ?_⟩
    intro a
    have hstar := mme_primary_hash_family_sharedZ_star_grading_components
      (grading K q) family a
    refine ⟨hstar.1, ?_⟩
    intro h
    exact (mme_complete_split_112_exact_address_MM_dimensions
      (K := K) q N L G (componentExactAddress family a h)).trans (hstar.2 h)
