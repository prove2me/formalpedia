-- Prove2me | solution 1 for mme_stothers_phi233_exact_component_product_restrict_outer_address_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:26:05.465776+00:00
-- url     : https://prove2.me/submissions/9e4813d8-7b48-4914-940f-eafd9936409d

import Mathlib.Tactic
import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_stothers_phi233_exact_label
import Theorems.Thm_mme_stothers_phi233_exact_profile_fine_factorization
import Theorems.Thm_mme_stothers_phi233_exact_fine_word_restrict_outer_address_block

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] (q : ℕ)
    {N alpha beta gamma delta : ℕ}
    (address : MME.StothersFourth.Phi233.ExactProfileAddress
      N alpha beta gamma delta) :
    TensorObj.Restrict
      (TensorObj.kronFin 10 (fun r ↦
        (MME.StothersFourth.Phi233.componentObj K q r).kronPow
          (MME.StothersFourth.Phi233.profileMultiplicity
            alpha beta gamma delta r)))
      (gradedAddressBlock
        (MME.StothersFourth.Phi233.outerGrading K q) address.1.1) := by
  exact TensorObj.Restrict.trans
    (mme_stothers_phi233_exact_profile_fine_factorization
      (K := K) q address)
    (mme_stothers_phi233_exact_fine_word_restrict_outer_address_block
      (K := K) q address)
