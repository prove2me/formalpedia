-- Prove2me | Theorems.Thm_mme_stothers_phi116_fine_component_restrictions
-- name    : mme_stothers_phi116_fine_component_restrictions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T19:28:41.196832+00:00
-- url     : https://prove2.me/theorems/c74c9ab5-0137-4140-bace-07d451879369
-- title:
--   Four literal fine components of the Davie--Stothers phi_116 constituent
-- statement:
--   Inside the product grading of $CW_6^{\otimes4}$, the four ordered fine blocks refining $\varphi_{116}$ satisfy
--
--   $$
--   013\otimes103,\ 103\otimes013 \;\ge\; \langle12,1,12\rangle,\qquad
--   004\otimes112,\ 112\otimes004 \;\ge\; D_6,
--   $$
--
--   where $D_6$ is the coupled $q=6$ square constituent and $\ge$ denotes that the tensor on the right is a restriction of the literal source block.
--
--   These four restrictions are the algebraic constituents in the outer extraction for Lemma 5.1(i). Because each source is a block of the product grading rather than an independent external copy, the statement preserves the ambient-variable structure needed for hashing.
-- source:
--   A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 21, https://era.ed.ac.uk/bitstream/1842/4734/1/Stothers2010.pdf; A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(i), printed pp. 363-364, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi116_fine_blocks
import Definitions.Def_mme_tensor_bridge

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi116_fine_component_restrictions
    {K : Type u} [Field K] :
    TensorObj.Restrict (MMObj K 12 1 12)
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K 6 0 1 3 1 0 3) ∧
    TensorObj.Restrict (MMObj K 12 1 12)
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K 6 1 0 3 0 1 3) ∧
    TensorObj.Restrict (coupledObj K 6)
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K 6 0 0 4 1 1 2) ∧
    TensorObj.Restrict (coupledObj K 6)
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K 6 1 1 2 0 0 4) := by
  sorry
