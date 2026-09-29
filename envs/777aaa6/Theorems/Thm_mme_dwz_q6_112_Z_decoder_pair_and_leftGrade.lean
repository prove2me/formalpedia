-- Prove2me | Theorems.Thm_mme_dwz_q6_112_Z_decoder_pair_and_leftGrade
-- name    : mme_dwz_q6_112_Z_decoder_pair_and_leftGrade
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T07:11:35.729063+00:00
-- url     : https://prove2.me/theorems/4065ed73-5ca1-4e74-9692-f3d1df70301b
-- title:
--   Exact canonical-pair inverse and grade translation for q=6 row 112
-- statement:
--   Every canonical coarse-grade-two Z-basis pair in the q=6 row-112 block decodes to a unique coordinate of the coupled constituent, and re-encoding gives the original pair. Under this decoder, the canonical left fine grade is exactly the enhanced-112 translation of the coupled internal grade. Thus the two exceptional coordinates and the 6 by 6 middle grid carry precisely the three prescribed left-grade classes used by the Table-2 projector.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Table 2 and enhanced 112 analysis in Section 6.3; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_q6_112_coupled_profile_data

open MME
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option maxHeartbeats 400000

theorem mme_dwz_q6_112_Z_decoder_pair_and_leftGrade
    (p : LiftedCoarsePair.{u} 6 2) :
    dwzCanonical112Pair 6 2 (dwzQ6Canonical112ZCoord p) = p.down.1 ∧
    p.leftGrade =
      mme_dwz_q6_coupled_Z_leftGrade
        (dwzQ6CoupledCoordGrade 2 (dwzQ6Canonical112ZCoord p)) := by
  sorry
