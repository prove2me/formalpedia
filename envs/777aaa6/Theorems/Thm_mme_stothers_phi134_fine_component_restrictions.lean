-- Prove2me | Theorems.Thm_mme_stothers_phi134_fine_component_restrictions
-- name    : mme_stothers_phi134_fine_component_restrictions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:43:25.428845+00:00
-- url     : https://prove2.me/theorems/84b74ac6-5d5a-4a8f-b64d-ddf9a044ce6a
-- title:
--   Literal fine-component atlas for phi_134
-- statement:
--   For every field and CW parameter $q$, the eight literal ordered square-block pairs of $\varphi_{134}$ admit the concrete restrictions used in Davie--Stothers Lemma 5.1(iii). The two endpoint pairs are rectangular tensors of volume $2q$; the two $(031,103)$ orientations are $\langle2q,1,2q\rangle$; and the remaining four pairs retain one correctly oriented coupled constituent together with a factor of volume $2q$ or $q^2+2$. The conclusion concerns the actual fine blocks of the literal fourth power.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(iii), printed p. 365, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi116_fine_blocks
import Definitions.Def_mme_tensor_bridge
import Definitions.Def_mme_permutation
import Definitions.Def_mme_CW_coupled_value

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi134_fine_component_restrictions
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict (MMObj K 1 (2 * q) 1)
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K q 0 0 4 1 3 0) ∧
    TensorObj.Restrict
      (TensorObj.kron (MMObj K 1 1 (2 * q))
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q)))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K q 0 1 3 1 2 1) ∧
    TensorObj.Restrict
      (TensorObj.kron (MMObj K 1 1 (q ^ 2 + 2)) (coupledObj K q))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K q 0 2 2 1 1 2) ∧
    TensorObj.Restrict (MMObj K (2 * q) 1 (2 * q))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K q 0 3 1 1 0 3) ∧
    TensorObj.Restrict (MMObj K (2 * q) 1 (2 * q))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K q 1 0 3 0 3 1) ∧
    TensorObj.Restrict
      (TensorObj.kron (coupledObj K q) (MMObj K 1 1 (q ^ 2 + 2)))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K q 1 1 2 0 2 2) ∧
    TensorObj.Restrict
      (TensorObj.kron
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q))
        (MMObj K 1 1 (2 * q)))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K q 1 2 1 0 1 3) ∧
    TensorObj.Restrict (MMObj K 1 (2 * q) 1)
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K q 1 3 0 0 0 4) := by
  sorry
