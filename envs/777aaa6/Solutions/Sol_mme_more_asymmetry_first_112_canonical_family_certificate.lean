-- Prove2me | solution 1 for mme_more_asymmetry_first_112_canonical_family_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-06T22:38:13.065723+00:00
-- url     : https://prove2.me/submissions/cb322d79-5f43-4174-95df-efeb28b3a72b

import Theorems.Thm_mme_more_asymmetry_first_active_112_profile_source_certificate
import Theorems.Thm_mme_complete_split_112_canonical_profile_router
import Definitions.Def_mme_complete_split_112_coupled_grading_data
import Definitions.Def_mme_TypeGrading_kron
import Theorems.Thm_mme_complete_split_112_disallowed_word_mismatches_exact_address
import Theorems.Thm_mme_complete_split_112_coupled_basis_label_certificate
import Theorems.Thm_mme_complete_split_112_concrete_four_block_certificate
import Theorems.Thm_mme_complete_split_primary_hash_family_restricted_Ctensor_certificate

open MME MME.CompleteSplit MME.CompleteSplit112 MME.DWZComponentRestriction
open CoupledCTensorPackaging
open scoped NNReal

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem actual_coupled_certificate
    {K : Type u} [Field K] (q : ℕ) {N L G A H : ℕ}
    (p : ℚ) (hLG : L + G = N) (hLp : (L : ℚ) = (2 * N : ℕ) * p)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (beta : Fin 3 → Profile 2)
    (hbeta : ∀ mode sigma,
      (beta mode).probability sigma = (profileProbability p mode sigma : ℝ))
    (epsilon : ℝ≥0) :
    Nonempty
      (CTensorOneHOneFamilyCertificate
        (restrictedPower (coupledObj K q) (liftedCoordBasis K q)
          (fun mode ↦ fineWord mode ∘ liftedCoordGrade q mode)
          beta epsilon (2 * N))
        A H (q ^ (4 * G + 2 * L))) := by
  obtain ⟨hSupport, h000, h111, h012, h102⟩ :=
    mme_complete_split_112_concrete_four_block_certificate (K := K) q
  apply mme_complete_split_primary_hash_family_restricted_Ctensor_certificate
    (T := coupledObj K q) (ell := 2)
    q (grading K q) family hSupport h000 h111 h012 h102
    (liftedCoordBasis K q) (liftedCoordGrade q) ?_
    (fun mode ↦ fineWord mode ∘ liftedCoordGrade q mode) beta epsilon ?_
  · intro mode a j hne
    exact TensorObj.TypeGrading.blockProj_apply_mem_ne
      (grading K q) mode a (liftedCoordGrade q mode j) hne.symm
      (liftedCoordBasis K q mode j)
      ((mme_complete_split_112_coupled_basis_label_certificate K q).2.2.2 mode j)
  · intro mode w hnot a h
    exact mme_complete_split_112_disallowed_word_mismatches_exact_address.1
      N L G p hLG hLp mode (liftedCoordGrade q mode) (beta mode)
      (hbeta mode) epsilon w hnot (componentExactAddress family a h)

/-- The released first active profile supports the actual retained family
inside the literal canonical q5 source, not just an unrestricted substitute. -/
theorem solution :
    ∃ beta : Fin 3 → Profile 2,
      (∀ mode sigma, (beta mode).probability sigma =
        (MoreAsymmetryFirstSlice.probability 0 mode sigma : ℝ)) ∧
      ∀ (K : Type u) [Field K] (m A H : ℕ)
        (_family : CWQ6PrimaryHashFamily
          (1180591620717411303424 * m)
          (8959763742786037 * m)
          (1180582660953668517387 * m) A H)
        (epsilon : ℝ≥0),
        Nonempty
          (CTensorOneHOneFamilyCertificate
            (restrictedCanonicalPower K 5 beta epsilon
              (2 * (1180591620717411303424 * m)))
            A H (5 ^ (4 * (1180582660953668517387 * m) +
              2 * (8959763742786037 * m)))) := by
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
  obtain ⟨certificate⟩ :=
    actual_coupled_certificate
      (K := K) 5 MoreAsymmetryFirstSlice.split0 hLG hLp family (beta 0) hprofile epsilon
  exact ⟨{
    star := certificate.star
    restrict := certificate.restrict.trans
      (mme_complete_split_112_canonical_profile_router K 5 (beta 0) epsilon
        (2 * (1180591620717411303424 * m)))
    certificate := certificate.certificate
  }⟩
