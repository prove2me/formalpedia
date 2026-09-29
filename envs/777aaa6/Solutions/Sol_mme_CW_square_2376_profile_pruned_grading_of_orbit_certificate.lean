-- Prove2me | solution 1 for mme_CW_square_2376_profile_pruned_grading_of_orbit_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T17:12:26.060415+00:00
-- url     : https://prove2.me/submissions/3118425d-d38f-4d8a-b751-44d0c31c5186

import Theorems.Thm_mme_CW_2376_exact_profile_induced_family
import Theorems.Thm_mme_CW_2376_exact_profile_induced_family_tensor_realization

open MME Filter

set_option autoImplicit false

universe u

theorem solution
    {K : Type u} [Field K]
    (cert : CWSquareFiveGradeCertificate K 6) :
    ∀ᶠ m : ℕ in atTop,
      ∃ (P : TensorObj K 3) (t : ℕ) (grading : P.TypeGrading t)
          (C : Finset (Fin 3 → Fin t))
          (σs : Fin C.card → (Fin 3 → Fin t)),
        TensorObj.Restrict P
            ((CWObj K 6).kronPow (6000000 * m)) ∧
        (∀ j, σs j ∈ C) ∧
        Function.Injective σs ∧
        (∀ σ ∈ C, ∀ σ' ∈ C, σ ≠ σ' →
          ∀ i : Fin 3, σ i ≠ σ' i) ∧
        (∀ σ : Fin 3 → Fin t, σ ∉ C →
          grading.blockTensor σ = 0) ∧
        (∀ j, TensorObj.Restrict (cw2376ProfileCore K m)
          (grading.blockSubtensor (σs j))) ∧
        (cw2376ProfileCountBase *
            Real.exp (-(cw2376ProfileRate m))) ^
            (3000000 * m) ≤ (C.card : ℝ) := by
  filter_upwards [mme_CW_2376_exact_profile_induced_family]
    with m hm
  obtain ⟨F, hF, hcount⟩ := hm
  obtain ⟨P, t, grading, C, σs, hP, hmem, hinj,
    hdisj, hsupp, hblocks, hcard⟩ :=
    mme_CW_2376_exact_profile_induced_family_tensor_realization cert m F hF
  refine ⟨P, t, grading, C, σs, ?_, hmem, hinj,
    hdisj, hsupp, hblocks, ?_⟩
  · have hpow : 2 * cw2376ProfileLength m = 6000000 * m := by
      unfold cw2376ProfileLength
      omega
    simpa [hpow] using hP
  · simpa [cw2376ProfileLength, hcard] using hcount
