-- Prove2me | solution 1 for mme_stothers_phi125_fine_component_restrictions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:41:22.063832+00:00
-- url     : https://prove2.me/submissions/cb9cdeac-c54c-4802-9754-4892b2bd018a

import Definitions.Def_mme_stothers_phi116_fine_blocks
import Definitions.Def_mme_tensor_bridge
import Theorems.Thm_mme_CW_square_canonical_elementary_blocks
import Theorems.Thm_mme_CW_square_canonical_coupled112_restrict
import Theorems.Thm_mme_CW_square_canonical_coupled121_restrict
import Theorems.Thm_mme_TypeGrading_kron_blockSubtensor_iso

open MME
open MME.TensorObj.TypeGrading

universe u

namespace MME.StothersFourth.Phi125

set_option autoImplicit false

private theorem kron_restrict
    {K : Type u} [Field K] {d : ℕ}
    {X X' Y Y' : TensorObj K d}
    (hd : 1 < d)
    (hX : TensorObj.Restrict X X')
    (hY : TensorObj.Restrict Y Y') :
    TensorObj.Restrict (TensorObj.kron X Y) (TensorObj.kron X' Y') := by
  let P := TensorQ.tensorStrassen K d hd
  have hx : P.le (TensorQ.toQ X) (TensorQ.toQ X') := hX
  have hy : P.le (TensorQ.toQ Y) (TensorQ.toQ Y') := hY
  have hleft := P.mul_right _ _ hx (TensorQ.toQ Y)
  have hright := P.mul_right _ _ hy (TensorQ.toQ X')
  exact P.le_trans _ _ _ hleft (by simpa [mul_comm] using hright)

private theorem scalar_left_kron_iso
    {K : Type u} [Field K] (X : TensorObj K 3) :
    TensorObj.Isomorphic (TensorObj.kron (MMObj K 1 1 1) X) X := by
  apply TensorQ.toQ_eq_iff.mp
  rw [TensorQ.toQ_kron]
  change MMq K 1 1 1 * TensorQ.toQ X = TensorQ.toQ X
  rw [MMq_one, one_mul]

private theorem scalar_right_kron_iso
    {K : Type u} [Field K] (X : TensorObj K 3) :
    TensorObj.Isomorphic (TensorObj.kron X (MMObj K 1 1 1)) X := by
  apply TensorQ.toQ_eq_iff.mp
  rw [TensorQ.toQ_kron]
  change TensorQ.toQ X * MMq K 1 1 1 = TensorQ.toQ X
  rw [MMq_one, mul_one]

private theorem fine_block_iso
    {K : Type u} [Field K] (q : ℕ)
    (I₁ J₁ L₁ I₂ J₂ L₂ : Fin 5) :
    TensorObj.Isomorphic
      (TensorObj.kron
        ((cwSquareCanonicalGrading K q).blockSubtensor
          (cwSquareBlockType I₁ J₁ L₁))
        ((cwSquareCanonicalGrading K q).blockSubtensor
          (cwSquareBlockType I₂ J₂ L₂)))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj
        K q I₁ J₁ L₁ I₂ J₂ L₂) := by
  exact mme_TypeGrading_kron_blockSubtensor_iso
    (cwSquareCanonicalGrading K q) (cwSquareCanonicalGrading K q)
    (cwSquareBlockType I₁ J₁ L₁) (cwSquareBlockType I₂ J₂ L₂)

/-- The six literal square-pair components of `phi_125`, before the outer
word extraction.  This is uniform in the CW parameter `q`. -/
theorem fine_component_restrictions
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj
        K q 0 0 4 1 2 1) ∧
    TensorObj.Restrict
      (TensorObj.kron (MMObj K 1 1 (2 * q)) (coupledObj K q))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj
        K q 0 1 3 1 1 2) ∧
    TensorObj.Restrict (MMObj K (2 * q) 1 (q ^ 2 + 2))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj
        K q 0 2 2 1 0 3) ∧
    TensorObj.Restrict (MMObj K (2 * q) 1 (q ^ 2 + 2))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj
        K q 1 0 3 0 2 2) ∧
    TensorObj.Restrict
      (TensorObj.kron (coupledObj K q) (MMObj K 1 1 (2 * q)))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj
        K q 1 1 2 0 1 3) ∧
    TensorObj.Restrict
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj
        K q 1 2 1 0 0 4) := by
  obtain ⟨_, h004, _, _, h013, _, h103, _, _, _, h022, _, _⟩ :=
    mme_CW_square_canonical_elementary_blocks (K := K) q
  have h112 := mme_CW_square_canonical_coupled112_restrict (K := K) q
  have h121 := mme_CW_square_canonical_coupled121_restrict (K := K) q
  constructor
  · have hproduct := kron_restrict (K := K) (d := 3) (by norm_num) h004 h121
    exact TensorObj.Restrict.trans
      (scalar_left_kron_iso
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q))).2 <|
      TensorObj.Restrict.trans hproduct (fine_block_iso (K := K) q 0 0 4 1 2 1).1
  constructor
  · exact TensorObj.Restrict.trans
      (kron_restrict (K := K) (d := 3) (by norm_num) h013 h112) <|
        (fine_block_iso (K := K) q 0 1 3 1 1 2).1
  constructor
  · have hproduct := kron_restrict (K := K) (d := 3) (by norm_num) h022 h103
    have hmm : TensorObj.Restrict (MMObj K (2 * q) 1 (q ^ 2 + 2))
        (TensorObj.kron (MMObj K 1 1 (q ^ 2 + 2))
          (MMObj K (2 * q) 1 1)) := by
      simpa using
        (MMObj_kron_iso (K := K) 1 1 (q ^ 2 + 2) (2 * q) 1 1).2
    exact TensorObj.Restrict.trans hmm <|
      TensorObj.Restrict.trans hproduct (fine_block_iso (K := K) q 0 2 2 1 0 3).1
  constructor
  · have hproduct := kron_restrict (K := K) (d := 3) (by norm_num) h103 h022
    have hmm : TensorObj.Restrict (MMObj K (2 * q) 1 (q ^ 2 + 2))
        (TensorObj.kron (MMObj K (2 * q) 1 1)
          (MMObj K 1 1 (q ^ 2 + 2))) := by
      simpa using
        (MMObj_kron_iso (K := K) (2 * q) 1 1 1 1 (q ^ 2 + 2)).2
    exact TensorObj.Restrict.trans hmm <|
      TensorObj.Restrict.trans hproduct (fine_block_iso (K := K) q 1 0 3 0 2 2).1
  constructor
  · exact TensorObj.Restrict.trans
      (kron_restrict (K := K) (d := 3) (by norm_num) h112 h013) <|
        (fine_block_iso (K := K) q 1 1 2 0 1 3).1
  · have hproduct := kron_restrict (K := K) (d := 3) (by norm_num) h121 h004
    exact TensorObj.Restrict.trans
      (scalar_right_kron_iso
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q))).2 <|
      TensorObj.Restrict.trans hproduct (fine_block_iso (K := K) q 1 2 1 0 0 4).1

end MME.StothersFourth.Phi125

theorem solution
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj
        K q 0 0 4 1 2 1) ∧
    TensorObj.Restrict
      (TensorObj.kron (MMObj K 1 1 (2 * q)) (coupledObj K q))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj
        K q 0 1 3 1 1 2) ∧
    TensorObj.Restrict (MMObj K (2 * q) 1 (q ^ 2 + 2))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj
        K q 0 2 2 1 0 3) ∧
    TensorObj.Restrict (MMObj K (2 * q) 1 (q ^ 2 + 2))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj
        K q 1 0 3 0 2 2) ∧
    TensorObj.Restrict
      (TensorObj.kron (coupledObj K q) (MMObj K 1 1 (2 * q)))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj
        K q 1 1 2 0 1 3) ∧
    TensorObj.Restrict
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj
        K q 1 2 1 0 0 4) := by
  exact MME.StothersFourth.Phi125.fine_component_restrictions q
