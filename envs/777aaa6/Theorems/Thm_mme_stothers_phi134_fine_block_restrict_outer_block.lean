-- Prove2me | Theorems.Thm_mme_stothers_phi134_fine_block_restrict_outer_block
-- name    : mme_stothers_phi134_fine_block_restrict_outer_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-05T10:34:01.514202+00:00
-- url     : https://prove2.me/theorems/5102fc38-7470-4ec2-a407-9d6c3c617659
-- title:
--   Each phi_134 fine block is a block of its literal internal five-grading
-- statement:
--   Let $s_x,s_y$ be three-mode grade words for the two square factors inside the fourth Coppersmith--Winograd power. Assume their modewise sums equal the coarse grades $(1,3,4)$ of $\varphi_{134}$:
--
--   $$
--   (s_x)_i+(s_y)_i=(1,3,4)_i\qquad(i=0,1,2).
--   $$
--
--   Then the literal product-grading block indexed by $(s_x,s_y)$ is a restriction of the $s_x$-block in the internal five-grading of the actual coarse constituent $\varphi_{134}$. In particular, the outer address used by the hashing argument denotes genuine subspaces of the literal constituent rather than a formal replacement tensor.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Section 5 and Lemma 5.1(iii), printed pp. 365--366, especially the eight fine pieces inside T_{134}; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. See also A. J. Stothers, On the Complexity of Matrix Multiplication (2010), Chapter 4.3, Lemma 25.

import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_stothers_phi134_outer_grading

open MME TensorProduct Module

universe u

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

theorem mme_stothers_phi134_fine_block_restrict_outer_block
    {K : Type u} [Field K] (q : ℕ)
    (sx sy : Fin 3 → Fin 5)
    (hsum : ∀ s, (sx s).val + (sy s).val =
      (MME.StothersFourth.Phi134.modeTotalGrade s).val) :
    TensorObj.Restrict
      ((TensorObj.TypeGrading.kronGrading
        (cwSquareCanonicalGrading K q)
        (cwSquareCanonicalGrading K q)).blockSubtensor
          (fun s ↦ finProdFinEquiv (sx s, sy s)))
      ((MME.StothersFourth.Phi134.outerGrading K q).blockSubtensor sx) := by
  sorry
