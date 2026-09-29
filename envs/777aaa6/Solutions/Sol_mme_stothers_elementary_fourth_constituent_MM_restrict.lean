-- Prove2me | solution 1 for mme_stothers_elementary_fourth_constituent_MM_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:56:17.59766+00:00
-- url     : https://prove2.me/submissions/2c51dc9c-d829-4f47-a5f7-3f33321be8de

import Theorems.Thm_mme_CW_square_canonical_elementary_blocks
import Theorems.Thm_mme_CW_fourth_fine_block_restrict_of_factors
import Theorems.Thm_mme_CW_fourth_fine_block_restrict_coarse
import Theorems.Thm_mme_stothers_elementary_fourth_nontrivial_constituent_MM_restrict
import Definitions.Def_mme_tensor_bridge

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict (MMObj K 1 1 1)
        (MME.StothersFourth.cwFourthConstituent K q 0 0 8) ∧
    TensorObj.Restrict (MMObj K 1 1 (4 * q))
        (MME.StothersFourth.cwFourthConstituent K q 0 1 7) ∧
    TensorObj.Restrict (MMObj K 1 1 (6 * q ^ 2 + 4))
        (MME.StothersFourth.cwFourthConstituent K q 0 2 6) ∧
    TensorObj.Restrict (MMObj K 1 1 (4 * q * (q ^ 2 + 3)))
        (MME.StothersFourth.cwFourthConstituent K q 0 3 5) ∧
    TensorObj.Restrict (MMObj K 1 1
        (q ^ 4 + 12 * q ^ 2 + 6))
      (MME.StothersFourth.cwFourthConstituent K q 0 4 4) := by
  obtain ⟨_, h004, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    mme_CW_square_canonical_elementary_blocks (K := K) q
  have hfine := mme_CW_fourth_fine_block_restrict_of_factors
    (K := K) q 0 0 4 0 0 4 h004 h004
  have hmm : TensorObj.Restrict (MMObj K 1 1 1)
      (TensorObj.kron (MMObj K 1 1 1) (MMObj K 1 1 1)) := by
    simpa using (MMObj_kron_iso (K := K) 1 1 1 1 1 1).2
  have hcoarse := mme_CW_fourth_fine_block_restrict_coarse
    (K := K) q (cwSquareBlockType 0 0 4)
      (cwSquareBlockType 0 0 4)
      (MME.StothersFourth.cwFourthBlockType 0 0 8)
      (by intro s; fin_cases s <;> rfl)
  have h008 : TensorObj.Restrict (MMObj K 1 1 1)
      (MME.StothersFourth.cwFourthConstituent K q 0 0 8) :=
    hmm.trans (hfine.trans (by
      simpa only [MME.StothersFourth.Phi116.cwFourthFineBlockObj,
        MME.StothersFourth.Phi116.cwFourthFineType,
        MME.StothersFourth.cwFourthConstituent] using hcoarse))
  obtain ⟨h017, h026, h035, h044⟩ :=
    mme_stothers_elementary_fourth_nontrivial_constituent_MM_restrict
      (K := K) q
  exact ⟨h008, h017, h026, h035, h044⟩
