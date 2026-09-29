-- Prove2me | Theorems.Thm_mme_stothers_phi116_outer_component_restrictions
-- name    : mme_stothers_phi116_outer_component_restrictions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T19:34:41.870751+00:00
-- url     : https://prove2.me/theorems/9c37a707-44a1-4d9c-8d51-4b8b6319df43
-- title:
--   Literal outer component certificate for Davie--Stothers phi_116
-- statement:
--   For the outer three-grading of the literal constituent $\varphi_{116}\subset CW_6^{\otimes4}$, the four source blocks carry the restrictions
--
--   $$
--   (012)_{\rm out},\ (102)_{\rm out}\;\ge\;\langle12,1,12\rangle,\qquad
--   (000)_{\rm out},\ (111)_{\rm out}\;\ge\;D_6,
--   $$
--
--   where $D_6$ is the coupled $q=6$ constituent. These are the two rectangular and two recursive factors in the two-type outer extraction for Lemma 5.1(i).
--
--   The statement concerns four blocks of one grading on the actual fourth-power constituent. It therefore preserves the shared-variable structure required for address hashing, unlike an assertion about four unrelated external tensors.
-- source:
--   A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 21, https://era.ed.ac.uk/bitstream/1842/4734/1/Stothers2010.pdf; A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(i), printed pp. 363-364, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi116_outer_grading
import Definitions.Def_mme_tensor_bridge

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi116_outer_component_restrictions
    {K : Type u} [Field K] :
    TensorObj.Restrict (MMObj K 12 1 12)
      ((MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockSubtensor
        ![0, 1, 2]) ∧
    TensorObj.Restrict (MMObj K 12 1 12)
      ((MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockSubtensor
        ![1, 0, 2]) ∧
    TensorObj.Restrict (coupledObj K 6)
      ((MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockSubtensor
        ![0, 0, 0]) ∧
    TensorObj.Restrict (coupledObj K 6)
      ((MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockSubtensor
        ![1, 1, 1]) := by
  sorry
