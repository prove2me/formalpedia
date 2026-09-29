-- Prove2me | Definitions.Def_mme_stothers_phi116_fine_blocks
-- name    : mme_stothers_phi116_fine_blocks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-02T19:22:49.229689+00:00
-- url     : https://prove2.me/theorems/620b290b-bcb9-4949-998b-e7c0e41523a5
-- title:
--   Literal ordered square-block pairs inside the fourth CW power
-- statement:
--   For two canonical constituents of $CW_q^{\otimes2}$, this module defines their ordered Kronecker pair as the corresponding literal block of the product grading on $CW_q^{\otimes4}$. The six indices $(I_1,J_1,L_1,I_2,J_2,L_2)$ record the two square-block grades mode by mode.
--
--   In particular, the definition distinguishes the four ordered pieces $013\otimes103$, $103\otimes013$, $004\otimes112$, and $112\otimes004$ that refine the Davie--Stothers constituent $\varphi_{116}$. Keeping them as literal grading blocks preserves the shared ambient variables needed by the later outer hashing argument.
-- source:
--   A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 21, https://era.ed.ac.uk/bitstream/1842/4734/1/Stothers2010.pdf; A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(i), printed pp. 363-364, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_TypeGrading_kron

open MME
open MME.TensorObj.TypeGrading

universe u

namespace MME.StothersFourth.Phi116

set_option autoImplicit false

/-- The ordered pair of canonical square-block types inside `CW_q^4`. -/
def cwFourthFineType
    (I₁ J₁ L₁ I₂ J₂ L₂ : Fin 5) : Fin 3 → Fin (5 * 5) :=
  fun s => finProdFinEquiv
    (cwSquareBlockType I₁ J₁ L₁ s, cwSquareBlockType I₂ J₂ L₂ s)

/-- A literal ordered square-block pair in the product grading of `CW_q^4`. -/
noncomputable def cwFourthFineBlockObj
    (K : Type u) [Field K] (q : ℕ)
    (I₁ J₁ L₁ I₂ J₂ L₂ : Fin 5) : TensorObj K 3 :=
  (kronGrading (cwSquareCanonicalGrading K q)
      (cwSquareCanonicalGrading K q)).blockSubtensor
    (cwFourthFineType I₁ J₁ L₁ I₂ J₂ L₂)

end MME.StothersFourth.Phi116


