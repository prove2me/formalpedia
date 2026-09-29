-- Prove2me | Theorems.Thm_mme_stothers_phi125_fine_component_restrictions
-- name    : mme_stothers_phi125_fine_component_restrictions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:40:11.328217+00:00
-- url     : https://prove2.me/theorems/f388b64c-0f2b-4435-8ec3-df11a5f46e5d
-- title:
--   Literal fine-component atlas for phi_125
-- statement:
--   For every field and every Coppersmith--Winograd parameter $q$, the six literal ordered square-block pairs of $\varphi_{125}$ admit the expected concrete restrictions. The endpoint pairs $(004,121)$ and $(121,004)$ retain the cyclically oriented coupled constituent. The pairs $(013,112)$ and $(112,013)$ retain one rectangular factor of volume $2q$ together with the coupled constituent. Finally, $(022,103)$ and $(103,022)$ restrict to matrix-multiplication tensors of dimensions $\langle 2q,1,q^2+2\rangle$. These are restrictions of the actual product-grading blocks, not external surrogate summands.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), displayed expansion of phi_125 on printed p. 363 and Lemma 5.1(ii) on pp. 364-365, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi116_fine_blocks
import Definitions.Def_mme_permutation
import Definitions.Def_mme_CW_coupled_value

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi125_fine_component_restrictions
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K q 0 0 4 1 2 1) ∧
    TensorObj.Restrict
      (TensorObj.kron (MMObj K 1 1 (2 * q)) (coupledObj K q))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K q 0 1 3 1 1 2) ∧
    TensorObj.Restrict (MMObj K (2 * q) 1 (q ^ 2 + 2))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K q 0 2 2 1 0 3) ∧
    TensorObj.Restrict (MMObj K (2 * q) 1 (q ^ 2 + 2))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K q 1 0 3 0 2 2) ∧
    TensorObj.Restrict
      (TensorObj.kron (coupledObj K q) (MMObj K 1 1 (2 * q)))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K q 1 1 2 0 1 3) ∧
    TensorObj.Restrict
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q))
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K q 1 2 1 0 0 4) := by
  sorry
