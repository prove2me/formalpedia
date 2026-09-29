-- Prove2me | Theorems.Thm_mme_CW_fourth_fine_block_restrict_of_factors
-- name    : mme_CW_fourth_fine_block_restrict_of_factors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:41:31.102568+00:00
-- url     : https://prove2.me/theorems/ac135995-3e82-40ca-b108-3a0d09639bff
-- title:
--   Factorwise restrictions realize literal fourth-power fine blocks
-- statement:
--   Let two tensors restrict to specified canonical blocks of the square Coppersmith--Winograd tensor. Their Kronecker product then restricts to the corresponding literal ordered fine block inside the fourth power. This theorem is uniform in $q$ and in all six square-grade coordinates. It provides the common tensor-functoriality bridge used by the Davie--Stothers $116$, $125$, $134$, $224$, and $233$ component atlases, and can also be reused for the q=5 fourth-power source.
-- source:
--   Functoriality of tensor restriction, applied to the ordered square-block decompositions in Davie--Stothers (2013), Section 5, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi116_fine_blocks

open MME

universe u

set_option autoImplicit false

theorem mme_CW_fourth_fine_block_restrict_of_factors
    {K : Type u} [Field K] (q : ℕ)
    (I₁ J₁ L₁ I₂ J₂ L₂ : Fin 5)
    {X Y : TensorObj K 3}
    (hX : TensorObj.Restrict X
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType I₁ J₁ L₁)))
    (hY : TensorObj.Restrict Y
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType I₂ J₂ L₂))) :
    TensorObj.Restrict (TensorObj.kron X Y)
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj
        K q I₁ J₁ L₁ I₂ J₂ L₂) := by
  sorry
