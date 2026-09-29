-- Prove2me | solution 1 for mme_CW_square_2376_profile_finite_hash_of_orbit_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T16:59:23.662826+00:00
-- url     : https://prove2.me/submissions/8ea9cfdc-67d5-46bc-8586-f7bcd7557a65

import Theorems.Thm_mme_CW_square_2376_profile_pruned_grading_of_orbit_certificate
import Theorems.Thm_mme_independent_blocks_form_direct_sum_restrict_enum_genDim
import Theorems.Thm_mme_bigAdd_mono_restrict

open MME Filter

set_option autoImplicit false

universe u

theorem solution
    {K : Type u} [Field K]
    (cert : CWSquareFiveGradeCertificate K 6) :
    ∀ᶠ m : ℕ in atTop,
      ∃ s : ℕ,
        TensorObj.Restrict
          (TensorObj.bigAdd
            (fun _ : Fin s => cw2376ProfileCore K m))
          ((CWObj K 6).kronPow (6000000 * m)) ∧
        (cw2376ProfileCountBase *
            Real.exp (-(cw2376ProfileRate m))) ^
            (3000000 * m) ≤ (s : ℝ) := by
  filter_upwards
    [mme_CW_square_2376_profile_pruned_grading_of_orbit_certificate cert]
      with m hm
  obtain ⟨P, t, grading, C, σs, hP, hmem, hinj,
    hdisj, hsupp, hblocks, hcount⟩ := hm
  refine ⟨C.card, ?_, hcount⟩
  have hindependent :=
    mme_independent_blocks_form_direct_sum_restrict_enum_genDim
      grading C σs hmem hinj hdisj hsupp
  exact TensorObj.Restrict.trans
    (mme_bigAdd_mono_restrict hblocks)
    (TensorObj.Restrict.trans hindependent hP)
