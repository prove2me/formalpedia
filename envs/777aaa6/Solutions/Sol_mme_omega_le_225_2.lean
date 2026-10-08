-- Prove2me | solution 2 for mme_omega_le_225
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T07:39:29.430439+00:00
-- url     : https://prove2.me/submissions/971f0a80-c4a7-4c0c-ad46-ed5f9b40f3c5

import Theorems.Thm_MMEBridge_matMulExp_le_exactRankExponent
import Theorems.Thm_OAI_MatrixMultiplication_AuxiliarySeparation_exactRankExponent_le_nine_quarters_allFields
import Mathlib.Tactic.NormNum

universe u

theorem solution {K : Type u} [Field K] :
    MME.matMulExp K ≤ (2.25 : ℝ) := by
  have h := (MMEBridge.matMulExp_le_exactRankExponent (K := K)).trans
    (OAI.MatrixMultiplication.AuxiliarySeparation.exactRankExponent_le_nine_quarters_allFields K)
  exact h.trans_eq (by norm_num)
