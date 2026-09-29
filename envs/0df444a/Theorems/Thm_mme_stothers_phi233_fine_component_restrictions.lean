-- Prove2me | Theorems.Thm_mme_stothers_phi233_fine_component_restrictions
-- name    : mme_stothers_phi233_fine_component_restrictions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:46:03.337731+00:00
-- url     : https://prove2.me/theorems/b6f2ace1-1f64-4f7e-bf0a-1799ebd95d61
-- title:
--   Literal fine-component atlas for phi_233
-- statement:
--   For every field and CW parameter $q$, the ten literal ordered square-pair components of $\varphi_{233}$ admit the exact concrete restrictions used before the nontrivial same-marginal extraction in Davie--Stothers Lemma 5.1(v). Six pairs are ordinary matrix-multiplication tensors with the displayed products of the $2q$ and $q^2+2$ dimensions; four pairs retain products of central or coupled constituents in their correct cyclic orientations. The theorem works with the actual product-grading blocks.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(v), printed p. 366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi116_fine_blocks
import Definitions.Def_mme_tensor_bridge
import Definitions.Def_mme_permutation
import Definitions.Def_mme_CW_coupled_value

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi233_fine_component_restrictions
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict (MMObj K 1 (q ^ 2 + 2) (2 * q))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K q 0 1 3 2 2 0) ∧
    TensorObj.Restrict
      (TensorObj.kron (MMObj K 1 1 (q ^ 2 + 2))
        (TensorObj.permObj cyclicPerm (coupledObj K q)))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K q 0 2 2 2 1 1) ∧
    TensorObj.Restrict (MMObj K (q ^ 2 + 2) 1 (2 * q))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K q 0 3 1 2 0 2) ∧
    TensorObj.Restrict (MMObj K (2 * q) (2 * q) 1)
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K q 1 0 3 1 3 0) ∧
    TensorObj.Restrict
      (TensorObj.kron (coupledObj K q)
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q)))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K q 1 1 2 1 2 1) ∧
    TensorObj.Restrict
      (TensorObj.kron
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q))
        (coupledObj K q))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K q 1 2 1 1 1 2) ∧
    TensorObj.Restrict (MMObj K (2 * q) (2 * q) 1)
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K q 1 3 0 1 0 3) ∧
    TensorObj.Restrict (MMObj K (q ^ 2 + 2) 1 (2 * q))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K q 2 0 2 0 3 1) ∧
    TensorObj.Restrict
      (TensorObj.kron
        (TensorObj.permObj cyclicPerm (coupledObj K q))
        (MMObj K 1 1 (q ^ 2 + 2)))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K q 2 1 1 0 2 2) ∧
    TensorObj.Restrict (MMObj K 1 (q ^ 2 + 2) (2 * q))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K q 2 2 0 0 1 3) := by
  sorry
