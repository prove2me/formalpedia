-- Prove2me | solution 1 for mme_CW_fourth_fine_block_restrict_of_factors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:43:26.770683+00:00
-- url     : https://prove2.me/submissions/d1d561fa-ea25-499d-9b03-c6a147c5159a

import Definitions.Def_mme_stothers_phi116_fine_blocks
import Theorems.Thm_mme_TypeGrading_kron_blockSubtensor_iso

open MME

universe u

set_option autoImplicit false

theorem solution
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
  let P := TensorQ.tensorStrassen K 3 (by norm_num)
  have hx : P.le (TensorQ.toQ X)
      (TensorQ.toQ
        ((cwSquareCanonicalGrading K q).blockSubtensor
          (cwSquareBlockType I₁ J₁ L₁))) := hX
  have hy : P.le (TensorQ.toQ Y)
      (TensorQ.toQ
        ((cwSquareCanonicalGrading K q).blockSubtensor
          (cwSquareBlockType I₂ J₂ L₂))) := hY
  have hleft := P.mul_right _ _ hx (TensorQ.toQ Y)
  have hright := P.mul_right _ _ hy
    (TensorQ.toQ
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType I₁ J₁ L₁)))
  have hproduct : TensorObj.Restrict (TensorObj.kron X Y)
      (TensorObj.kron
        ((cwSquareCanonicalGrading K q).blockSubtensor
          (cwSquareBlockType I₁ J₁ L₁))
        ((cwSquareCanonicalGrading K q).blockSubtensor
          (cwSquareBlockType I₂ J₂ L₂))) := by
    exact P.le_trans _ _ _ hleft (by simpa [mul_comm] using hright)
  exact TensorObj.Restrict.trans hproduct
    (mme_TypeGrading_kron_blockSubtensor_iso
      (cwSquareCanonicalGrading K q) (cwSquareCanonicalGrading K q)
      (cwSquareBlockType I₁ J₁ L₁) (cwSquareBlockType I₂ J₂ L₂)).1
