-- Prove2me | solution 1 for mme_recursive_yz_stage_source_exponent
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T09:11:25.210454+00:00
-- url     : https://prove2.me/submissions/ee0f978c-cfa7-483c-9c8c-9da44b2d8cb7

import Definitions.Def_mme_recursive_yz_stage_certificate

open BigOperators MME MME.RecursiveYZ MME.RecursiveYZ.Certificate

/-- Each hashed parent contributes two physical child positions. -/
theorem recursive_stage_position_count (D : HashExtraction.HashData) (A : Stage D) :
    A.L = 2 * (D.N + 1) := by
  have hparent := Fintype.card_congr D.positions
  have hchild := Fintype.card_congr A.positions
  simp only [Fintype.card_fin, Fintype.card_sigma] at hparent
  simp only [Position, Fintype.card_fin, Fintype.card_sigma,
    Fintype.card_prod] at hchild
  rw [← Finset.sum_mul] at hchild
  omega

/-- The literal CW source has one block of `D.half` factors per hashed parent. -/
theorem solution (D : HashExtraction.HashData) (A : Stage D) :
    A.L * 2 ^ (A.ell - 1) = (D.N + 1) * D.half := by
  rw [recursive_stage_position_count D A, A.half_eq]
  ring

