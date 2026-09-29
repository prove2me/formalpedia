-- Prove2me | Theorems.Thm_mme_dwz_q6_explicit_coupled_four_block_support
-- name    : mme_dwz_q6_explicit_coupled_four_block_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T08:12:52.856061+00:00
-- url     : https://prove2.me/theorems/786a530b-6de4-437f-b125-6c8aff3cd6a4
-- title:
--   Four-block support of the explicit q=6 coupled grading
-- statement:
--   The source-faithful explicit three-grading of the q=6 coupled constituent has exactly four supported block types: $(0,0,0)$, $(1,1,1)$, $(0,1,2)$, and $(1,0,2)$. Every other block tensor is zero. This is the local support condition required to prove that non-diagonal mixed choices vanish in shared-Z outer extraction.
-- source:
--   Coppersmith and Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), coupled constituent on pp. 270-272; Duan, Wu, and Zhou, arXiv:2210.10173v5, Section 6.3.

import Mathlib.Data.Fin.VecNotation
import Definitions.Def_mme_dwz_q6_coupled_explicit_grading

open MME
open MME.DWZComponentRestriction

universe u
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem mme_dwz_q6_explicit_coupled_four_block_support
    {K : Type u} [Field K]
    (σ : Fin 3 → Fin 3)
    (h000 : σ ≠ ![0, 0, 0])
    (h111 : σ ≠ ![1, 1, 1])
    (h012 : σ ≠ ![0, 1, 2])
    (h102 : σ ≠ ![1, 0, 2]) :
    (dwzQ6CoupledGrading K).blockTensor σ = 0 := by
  sorry
