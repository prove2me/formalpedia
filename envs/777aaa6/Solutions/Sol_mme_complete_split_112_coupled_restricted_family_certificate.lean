-- Prove2me | solution 1 for mme_complete_split_112_coupled_restricted_family_certificate
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-11T21:38:02.895227+00:00
-- url     : https://prove2.me/submissions/59763506-8c06-41b7-a02a-b9d7a0f4da66

-- Explicitly list the complete public dependency closure for server materialization.
-- Argument adapted from marwahaha's public submission 5c6cd215-8772-4364-893b-57545df0aabe.
import Definitions.Def_CTensorOneHOneCertificate
import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_CW_2376_address_block
import Definitions.Def_mme_CW_2376_profile_address
import Definitions.Def_mme_CW_2376_profile_data
import Definitions.Def_mme_CW_auxiliary_RHS
import Definitions.Def_mme_CW_auxiliary_RHS_coupled
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_CW_q6_primary_hash_family
import Definitions.Def_mme_CW_square_canonical_grading
import Definitions.Def_mme_CW_square_five_grade_certificate
import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_block_subtensor
import Definitions.Def_mme_block_tensor
import Definitions.Def_mme_complete_split_112_address_words
import Definitions.Def_mme_complete_split_112_coupled_grading_data
import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_coupled_Ctensor_outer_extraction_data
import Definitions.Def_mme_coupled_Ctensor_packaging_data
import Definitions.Def_mme_dwz_q6_canonical_112_router_data
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_flattening
import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_kron_pow_mode_word_basis
import Definitions.Def_mme_mmobj_mul
import Definitions.Def_mme_modern_entropy_data
import Definitions.Def_mme_more_asymmetry_first_112_profile_data
import Definitions.Def_mme_omega
import Definitions.Def_mme_omega_strassen
import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_strassen_preorder
import Definitions.Def_mme_tau_value
import Definitions.Def_mme_tensor
import Definitions.Def_mme_tensor_quotient
import Definitions.Def_mme_tensor_rank
import Definitions.Def_mme_tensor_type_grading
import Theorems.Thm_mme_complete_split_112_concrete_four_block_certificate
import Theorems.Thm_mme_complete_split_112_coupled_basis_label_certificate
import Theorems.Thm_mme_complete_split_112_disallowed_word_mismatches_exact_address
import Theorems.Thm_mme_complete_split_112_exact_address_histogram
import Theorems.Thm_mme_complete_split_primary_hash_family_restricted_Ctensor_certificate

set_option autoImplicit false
set_option warningAsError true

open MME MME.CompleteSplit MME.CompleteSplit112 MME.DWZComponentRestriction
open CoupledCTensorPackaging
open scoped NNReal

universe u

theorem solution
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
