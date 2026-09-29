-- Prove2me | Theorems.Thm_mme_CW_fourth_fine_block_restrict_coarse_block
-- name    : mme_CW_fourth_fine_block_restrict_coarse_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:52:35.400211+00:00
-- url     : https://prove2.me/theorems/6cfb2150-14f5-428a-8936-2375c09fabdb
-- title:
--   A compatible fine fourth-power block restricts from its coarse block
-- statement:
--   Let a fine block of the fourth Coppersmith--Winograd power be specified by two square-block grades $(I_1,J_1,L_1)$ and $(I_2,J_2,L_2)$. Suppose their modewise sums equal a coarse fourth-power grade $\kappa$:
--
--   $$
--   I_1+I_2=\kappa_0,\qquad J_1+J_2=\kappa_1,\qquad L_1+L_2=\kappa_2.
--   $$
--
--   Then the literal fine product-grading block is a tensor restriction of the coarse $\kappa$ block. This is the general source-faithful bridge needed to place the fine constituent decompositions for $\varphi_{125},\varphi_{134},\varphi_{224}$, and $\varphi_{233}$ inside their actual coarse fourth-power constituents.
-- source:
--   The canonical fine-to-coarse grading relation used throughout A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Section 5 and Table 1, pp. 365--368, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; formalized for the literal fourth Coppersmith--Winograd power.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi116_fine_blocks

open MME TensorProduct Module

universe u

set_option autoImplicit false

theorem mme_CW_fourth_fine_block_restrict_coarse_block
    {K : Type u} [Field K] (q : ℕ)
    (I₁ J₁ L₁ I₂ J₂ L₂ : Fin 5)
    (coarse : Fin 3 → Fin 9)
    (hsum : ∀ s,
      (cwSquareBlockType I₁ J₁ L₁ s).val +
          (cwSquareBlockType I₂ J₂ L₂ s).val =
        (coarse s).val) :
    TensorObj.Restrict
      (MME.StothersFourth.Phi116.cwFourthFineBlockObj
        K q I₁ J₁ L₁ I₂ J₂ L₂)
      ((MME.StothersFourth.cwFourthCanonicalGrading K q).blockSubtensor
        coarse) := by
  sorry
