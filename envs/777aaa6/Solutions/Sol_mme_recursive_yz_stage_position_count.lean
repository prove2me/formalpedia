-- Prove2me | solution 1 for mme_recursive_yz_stage_position_count
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T09:12:00.563548+00:00
-- url     : https://prove2.me/submissions/7e45cd33-7522-4d3f-b858-e03e99373a75

import Definitions.Def_mme_recursive_yz_stage_certificate

open BigOperators MME MME.RecursiveYZ MME.RecursiveYZ.Certificate

theorem solution (D : HashExtraction.HashData) (A : Stage D) :
    A.L = 2 * (D.N + 1) := by
  have hparent := Fintype.card_congr D.positions
  have hchild := Fintype.card_congr A.positions
  simp only [Fintype.card_fin, Fintype.card_sigma] at hparent
  simp only [Position, Fintype.card_fin, Fintype.card_sigma,
    Fintype.card_prod] at hchild
  rw [← Finset.sum_mul] at hchild
  omega
