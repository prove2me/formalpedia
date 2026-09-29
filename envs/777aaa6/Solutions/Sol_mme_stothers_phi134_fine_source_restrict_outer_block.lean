-- Prove2me | solution 1 for mme_stothers_phi134_fine_source_restrict_outer_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T10:49:00.638952+00:00
-- url     : https://prove2.me/submissions/d18d43f3-e3b6-4fd0-b432-5fdef40e9329

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi134_profile_data
import Definitions.Def_mme_stothers_phi134_outer_grading
import Theorems.Thm_mme_stothers_phi134_fine_block_restrict_outer_block

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] (q : ℕ) (r : Fin 8) :
    TensorObj.Restrict
      (MME.StothersFourth.Phi134.fineSourceObj K q r)
      ((MME.StothersFourth.Phi134.outerGrading K q).blockSubtensor
        (MME.StothersFourth.Phi134.pattern r)) := by
  fin_cases r
  · simpa only [MME.StothersFourth.Phi134.fineSourceObj,
      MME.StothersFourth.Phi134.pattern,
      MME.StothersFourth.Phi116.cwFourthFineBlockObj,
      MME.StothersFourth.Phi116.cwFourthFineType] using
      mme_stothers_phi134_fine_block_restrict_outer_block (K := K) q
        (cwSquareBlockType 0 0 4) (cwSquareBlockType 1 3 0)
        (by intro s; fin_cases s <;> rfl)
  · simpa only [MME.StothersFourth.Phi134.fineSourceObj,
      MME.StothersFourth.Phi134.pattern,
      MME.StothersFourth.Phi116.cwFourthFineBlockObj,
      MME.StothersFourth.Phi116.cwFourthFineType] using
      mme_stothers_phi134_fine_block_restrict_outer_block (K := K) q
        (cwSquareBlockType 0 1 3) (cwSquareBlockType 1 2 1)
        (by intro s; fin_cases s <;> rfl)
  · simpa only [MME.StothersFourth.Phi134.fineSourceObj,
      MME.StothersFourth.Phi134.pattern,
      MME.StothersFourth.Phi116.cwFourthFineBlockObj,
      MME.StothersFourth.Phi116.cwFourthFineType] using
      mme_stothers_phi134_fine_block_restrict_outer_block (K := K) q
        (cwSquareBlockType 0 2 2) (cwSquareBlockType 1 1 2)
        (by intro s; fin_cases s <;> rfl)
  · simpa only [MME.StothersFourth.Phi134.fineSourceObj,
      MME.StothersFourth.Phi134.pattern,
      MME.StothersFourth.Phi116.cwFourthFineBlockObj,
      MME.StothersFourth.Phi116.cwFourthFineType] using
      mme_stothers_phi134_fine_block_restrict_outer_block (K := K) q
        (cwSquareBlockType 0 3 1) (cwSquareBlockType 1 0 3)
        (by intro s; fin_cases s <;> rfl)
  · simpa only [MME.StothersFourth.Phi134.fineSourceObj,
      MME.StothersFourth.Phi134.pattern,
      MME.StothersFourth.Phi116.cwFourthFineBlockObj,
      MME.StothersFourth.Phi116.cwFourthFineType] using
      mme_stothers_phi134_fine_block_restrict_outer_block (K := K) q
        (cwSquareBlockType 1 0 3) (cwSquareBlockType 0 3 1)
        (by intro s; fin_cases s <;> rfl)
  · simpa only [MME.StothersFourth.Phi134.fineSourceObj,
      MME.StothersFourth.Phi134.pattern,
      MME.StothersFourth.Phi116.cwFourthFineBlockObj,
      MME.StothersFourth.Phi116.cwFourthFineType] using
      mme_stothers_phi134_fine_block_restrict_outer_block (K := K) q
        (cwSquareBlockType 1 1 2) (cwSquareBlockType 0 2 2)
        (by intro s; fin_cases s <;> rfl)
  · simpa only [MME.StothersFourth.Phi134.fineSourceObj,
      MME.StothersFourth.Phi134.pattern,
      MME.StothersFourth.Phi116.cwFourthFineBlockObj,
      MME.StothersFourth.Phi116.cwFourthFineType] using
      mme_stothers_phi134_fine_block_restrict_outer_block (K := K) q
        (cwSquareBlockType 1 2 1) (cwSquareBlockType 0 1 3)
        (by intro s; fin_cases s <;> rfl)
  · simpa only [MME.StothersFourth.Phi134.fineSourceObj,
      MME.StothersFourth.Phi134.pattern,
      MME.StothersFourth.Phi116.cwFourthFineBlockObj,
      MME.StothersFourth.Phi116.cwFourthFineType] using
      mme_stothers_phi134_fine_block_restrict_outer_block (K := K) q
        (cwSquareBlockType 1 3 0) (cwSquareBlockType 0 0 4)
        (by intro s; fin_cases s <;> rfl)
