-- Prove2me | Theorems.Thm_mme_stothers_phi116_outer_fine_block_restrictions
-- name    : mme_stothers_phi116_outer_fine_block_restrictions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T19:32:18.040841+00:00
-- url     : https://prove2.me/theorems/333c14a9-4404-40ef-aaad-d67e60194d73
-- title:
--   Exact tensor bridge from the phi_116 outer grading to its four fine blocks
-- statement:
--   For the literal outer three-grading of $\varphi_{116}\subset CW_6^{\otimes4}$, each of the four source-supported outer blocks restricts to its exact ordered fine square-block pair:
--
--   $$
--   013\otimes103\le(012)_{\rm out},\quad 103\otimes013\le(102)_{\rm out},\quad
--   004\otimes112\le(000)_{\rm out},\quad 112\otimes004\le(111)_{\rm out}.
--   $$
--
--   Here $\le$ is the Strassen restriction preorder. The maps are the canonical flattenings of the nested grading subspaces, and the statement identifies the actual block tensors rather than only matching their coordinate counts. This is the exact bridge needed to transfer the square-constituent certificates into the outer laser grading for Lemma 5.1(i).
-- source:
--   A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 21, https://era.ed.ac.uk/bitstream/1842/4734/1/Stothers2010.pdf; A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(i), printed pp. 363-364, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_phi116_outer_grading
import Definitions.Def_mme_stothers_phi116_fine_blocks

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi116_outer_fine_block_restrictions
    (K : Type u) [Field K] :
    TensorObj.Restrict
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K 6 0 1 3 1 0 3)
      ((MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockSubtensor
        ![0, 1, 2]) ∧
    TensorObj.Restrict
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K 6 1 0 3 0 1 3)
      ((MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockSubtensor
        ![1, 0, 2]) ∧
    TensorObj.Restrict
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K 6 0 0 4 1 1 2)
      ((MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockSubtensor
        ![0, 0, 0]) ∧
    TensorObj.Restrict
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj K 6 1 1 2 0 0 4)
      ((MME.StothersFourth.Phi116.cwPhi116ThreeGrading K).blockSubtensor
        ![1, 1, 1]) := by
  sorry
