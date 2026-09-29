-- Prove2me | solution 1 for mme_dwz_seven_eighths_certificate_has_literal_nonhole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T11:19:00.929623+00:00
-- url     : https://prove2.me/submissions/166e3680-8b07-45ab-8e03-4f19e40f7108

import Definitions.Def_mme_dwz_hole_cover_data

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {Block : Type*} [Fintype Block] [Nonempty Block]
    (copy : MME.DWZSquare.BrokenBlockCopy Block)
    (hseven :
      7 * Fintype.card Block ≤ 8 * copy.nonholes.card) :
    ∃ z : Block, z ∈ copy.nonholes := by
  have hBlock : 0 < Fintype.card Block :=
    Fintype.card_pos_iff.mpr inferInstance
  have hNonholes : 0 < copy.nonholes.card := by
    omega
  exact Finset.card_pos.mp hNonholes
