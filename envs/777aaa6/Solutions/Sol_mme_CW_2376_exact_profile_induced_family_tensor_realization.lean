-- Prove2me | solution 1 for mme_CW_2376_exact_profile_induced_family_tensor_realization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T17:19:19.039428+00:00
-- url     : https://prove2.me/submissions/5394eb7a-2101-4122-91a7-da865e4668f6

import Theorems.Thm_mme_CW_2376_induced_family_direct_sum_extraction
import Theorems.Thm_mme_diagObj_kron_canonical_grading_certificate
import Theorems.Thm_mme_kron_self_kronPow_isomorphic

open MME

set_option autoImplicit false

universe u

theorem solution
    {K : Type u} [Field K]
    (cert : CWSquareFiveGradeCertificate K 6)
    (m : ℕ) (F : Finset (CW2376ExactProfileAddress m))
    (hF : CW2376InducedModeDisjoint F) :
    ∃ (P : TensorObj K 3) (t : ℕ) (grading : P.TypeGrading t)
        (C : Finset (Fin 3 → Fin t))
        (σs : Fin C.card → (Fin 3 → Fin t)),
      TensorObj.Restrict P
          ((CWObj K 6).kronPow (2 * cw2376ProfileLength m)) ∧
      (∀ j, σs j ∈ C) ∧
      Function.Injective σs ∧
      (∀ σ ∈ C, ∀ σ' ∈ C, σ ≠ σ' →
        ∀ i : Fin 3, σ i ≠ σ' i) ∧
      (∀ σ : Fin 3 → Fin t, σ ∉ C →
        grading.blockTensor σ = 0) ∧
      (∀ j, TensorObj.Restrict (cw2376ProfileCore K m)
        (grading.blockSubtensor (σs j))) ∧
      C.card = F.card := by
  let P := TensorObj.kron (TensorObj.diagObj K 3 F.card)
    (cw2376ProfileCore K m)
  have hExtract :
      TensorObj.Restrict P
        ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow
          (cw2376ProfileLength m)) := by
    simpa [P] using
      mme_CW_2376_induced_family_direct_sum_extraction cert m F hF
  have hSquarePower :
      TensorObj.Restrict
        ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow
          (cw2376ProfileLength m))
        ((CWObj K 6).kronPow (2 * cw2376ProfileLength m)) :=
    (mme_kron_self_kronPow_isomorphic
      (CWObj K 6) (cw2376ProfileLength m)).1
  have hP :
      TensorObj.Restrict P
        ((CWObj K 6).kronPow (2 * cw2376ProfileLength m)) :=
    TensorObj.Restrict.trans hExtract hSquarePower
  obtain ⟨t, grading, C, σs, hmem, hinj, hdisj,
    hsupp, hblocks, hcard⟩ :=
    mme_diagObj_kron_canonical_grading_certificate
      (cw2376ProfileCore K m) F.card
  exact ⟨P, t, grading, C, σs, hP, hmem, hinj,
    hdisj, hsupp, hblocks, hcard⟩
