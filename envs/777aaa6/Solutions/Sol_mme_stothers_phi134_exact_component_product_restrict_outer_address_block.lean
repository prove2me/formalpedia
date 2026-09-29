-- Prove2me | solution 1 for mme_stothers_phi134_exact_component_product_restrict_outer_address_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T10:52:45.617306+00:00
-- url     : https://prove2.me/submissions/f3abd4ba-c2aa-479d-b5f3-a99c6b69c8a6

import Mathlib.Tactic
import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_stothers_phi134_exact_label
import Definitions.Def_mme_stothers_phi134_outer_grading
import Theorems.Thm_mme_stothers_phi134_exact_profile_fine_factorization
import Theorems.Thm_mme_stothers_phi134_exact_fine_word_restrict_outer_address_block

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] (q : ℕ)
    {N alpha beta gamma delta : ℕ}
    (address : MME.StothersFourth.Phi134.ExactProfileAddress
      N alpha beta gamma delta) :
    TensorObj.Restrict
      (TensorObj.kronFin 8 (fun r ↦
        (MME.StothersFourth.Phi134.componentObj K q r).kronPow
          (MME.StothersFourth.Phi134.profileMultiplicity
            alpha beta gamma delta r)))
      (gradedAddressBlock
        (MME.StothersFourth.Phi134.outerGrading K q) address.1.1) := by
  exact TensorObj.Restrict.trans
    (mme_stothers_phi134_exact_profile_fine_factorization
      (K := K) q address)
    (mme_stothers_phi134_exact_fine_word_restrict_outer_address_block
      (K := K) q address)
