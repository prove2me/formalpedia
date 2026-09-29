-- Prove2me | Theorems.Thm_mme_stothers_phi224_fine_component_restrictions
-- name    : mme_stothers_phi224_fine_component_restrictions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:45:02.644366+00:00
-- url     : https://prove2.me/theorems/f37b3a69-8a64-4e07-9738-cb691177a6c2
-- title:
--   Literal fine-component atlas for phi_224
-- statement:
--   For every field and CW parameter $q$, the nine literal square-pair components of $\varphi_{224}$ admit their source-faithful restrictions. The atlas includes the central pair $(112,112)$ as a product of two coupled constituents, the four mixed elementary--coupled pairs with their correct cyclic orientations, two $\langle q^2+2,1,q^2+2\rangle$ pairs, and two scalar-central endpoint pairs. This is the algebraic component input to Davie--Stothers Lemma 5.1(iv).
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(iv), printed pp. 365-366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi116_fine_blocks
import Definitions.Def_mme_tensor_bridge
import Definitions.Def_mme_permutation
import Definitions.Def_mme_CW_coupled_value

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi224_fine_component_restrictions
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict (MMObj K 1 (q ^ 2 + 2) 1)
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K q 0 0 4 2 2 0) ∧
    TensorObj.Restrict
      (TensorObj.kron (MMObj K 1 1 (2 * q))
        (TensorObj.permObj cyclicPerm (coupledObj K q)))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K q 0 1 3 2 1 1) ∧
    TensorObj.Restrict (MMObj K (q ^ 2 + 2) 1 (q ^ 2 + 2))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K q 0 2 2 2 0 2) ∧
    TensorObj.Restrict
      (TensorObj.kron (MMObj K (2 * q) 1 1)
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q)))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K q 1 0 3 1 2 1) ∧
    TensorObj.Restrict
      (TensorObj.kron (coupledObj K q) (coupledObj K q))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K q 1 1 2 1 1 2) ∧
    TensorObj.Restrict
      (TensorObj.kron
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q))
        (MMObj K (2 * q) 1 1))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K q 1 2 1 1 0 3) ∧
    TensorObj.Restrict (MMObj K (q ^ 2 + 2) 1 (q ^ 2 + 2))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K q 2 0 2 0 2 2) ∧
    TensorObj.Restrict
      (TensorObj.kron
        (TensorObj.permObj cyclicPerm (coupledObj K q))
        (MMObj K 1 1 (2 * q)))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K q 2 1 1 0 1 3) ∧
    TensorObj.Restrict (MMObj K 1 (q ^ 2 + 2) 1)
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K q 2 2 0 0 0 4) := by
  sorry
