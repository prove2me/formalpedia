-- Prove2me | solution 1 for mme_dwz_q6_112_restricted_primary_star_assembly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T08:43:56.25119+00:00
-- url     : https://prove2.me/submissions/4223e8a2-9ff7-4022-a605-6430c4f16a73

import Theorems.Thm_mme_dwz_q6_112_primary_hash_family_outer_restrict
import Theorems.Thm_mme_primary_hash_family_sharedZ_star_grading_components
import Definitions.Def_CTensorOneHOneCertificate

open MME
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] (m A H : ℕ)
    (family : CWQ6PrimaryHashFamily
      (50000000 * (20088623 * m))
      (21015 * (20088623 * m))
      (49978985 * (20088623 * m)) A H) :
    ∃ star : Fin A → TensorObj K 3,
      TensorObj.Restrict (TensorObj.bigAdd star)
        (restrictedComponentPower K (12 : Fin 15) m) ∧
      ∀ a : Fin A,
        ∃ starGrading : (star a).TypeGrading (H + 1),
          (∀ σ : Fin 3 → Fin (H + 1),
            σ ∉ Finset.univ.image (cTensorOneHOneAddress H) →
              starGrading.blockTensor σ = 0) ∧
          ∀ h : Fin H,
            TensorObj.Isomorphic
              (gradedAddressBlock (dwzQ6CoupledGrading K)
                (family.entry (a, h)).1)
              (starGrading.blockSubtensor
                (cTensorOneHOneAddress H h)) := by
  let G0 := dwzQ6CoupledGrading K
  let star := CoupledCTensorPackaging.starObj G0 family
  refine ⟨star,
    mme_dwz_q6_112_primary_hash_family_outer_restrict
      (K := K) m A H family, ?_⟩
  intro a
  refine ⟨CoupledCTensorPackaging.starGrading G0 family a, ?_⟩
  have hstar :=
    mme_primary_hash_family_sharedZ_star_grading_components
      G0 family a
  refine ⟨hstar.1, ?_⟩
  intro h
  simpa only [CoupledCTensorPackaging.componentObj,
    CoupledCTensorPackaging.componentAddress_eq_entry] using hstar.2 h
