-- Prove2me | Theorems.Thm_mme_dwz_q6_explicit_coupled_four_block_isomorphisms
-- name    : mme_dwz_q6_explicit_coupled_four_block_isomorphisms
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T07:46:07.769675+00:00
-- url     : https://prove2.me/theorems/e1da33c9-7373-4c7b-b6a1-0f9fd4de32f8
-- title:
--   Four matrix-multiplication blocks of the explicit q=6 coupled grading
-- statement:
--   For the explicit three-grading of the $q=6$ coupled four-sum constituent, the two diagonal supported blocks are each isomorphic to $\langle1,6,1\rangle$, while the two crossed supported blocks are each isomorphic to $\langle6,1,6\rangle$. These are the four local factors whose exact multiplicities in an enhanced-112 address give component volume $6^{4G+2L}$.
-- source:
--   Coppersmith and Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), coupled constituent on pp. 270-272; Duan, Wu, and Zhou, arXiv:2210.10173v5, enhanced 112 analysis in Section 6.3.

import Mathlib.Data.Fin.VecNotation
import Definitions.Def_mme_dwz_q6_coupled_explicit_grading
import Definitions.Def_mme_tensor_quotient

open MME
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_q6_explicit_coupled_four_block_isomorphisms
    {K : Type u} [Field K] :
    TensorObj.Isomorphic (MMObj K 1 6 1)
        ((dwzQ6CoupledGrading K).blockSubtensor ![0, 0, 0]) ∧
      TensorObj.Isomorphic (MMObj K 1 6 1)
        ((dwzQ6CoupledGrading K).blockSubtensor ![1, 1, 1]) ∧
      TensorObj.Isomorphic (MMObj K 6 1 6)
        ((dwzQ6CoupledGrading K).blockSubtensor ![0, 1, 2]) ∧
      TensorObj.Isomorphic (MMObj K 6 1 6)
        ((dwzQ6CoupledGrading K).blockSubtensor ![1, 0, 2]) := by
  sorry
