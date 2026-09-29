-- Prove2me | Theorems.Thm_mme_cyclic_triple_grading_nonzero_factors
-- name    : mme_cyclic_triple_grading_nonzero_factors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:26:31.368615+00:00
-- url     : https://prove2.me/theorems/953ed5d7-e36f-4a3f-a297-513d02d051b6
-- title:
--   A nonzero cyclic product block has three nonzero factor blocks
-- statement:
--   Let $G$ be a finite grading of a three-mode tensor $T$, and equip $T\otimes\pi T\otimes\pi^2T$ with the induced cyclic product grading. If the block indexed by three factor-grade triples $\rho_X,\rho_Y,\rho_Z$ is nonzero, then every corresponding factor block is nonzero:
--
--   $$
--   B_{\mathrm{cyc}}(\rho_X,\rho_Y,\rho_Z)\ne0
--   \quad\Longrightarrow\quad
--   B_G(\rho_X)\ne0,\;B_G(\rho_Y)\ne0,\;B_G(\rho_Z)\ne0.
--   $$
--
--   This support-reflection property converts nonvanishing in a cyclic tensor power into the three coordinatewise support conditions required by the type-2 hashing and induced-matching argument.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), support pruning in Lemma 5.1(v), pp. 366--367; https://www.maths.ed.ac.uk/~sandy/a11164.pdf. The implication itself is the standard support property of a tensor-product grading.

import Definitions.Def_mme_cyclic_triple_grading

open MME TensorObj.TypeGrading

universe u

set_option autoImplicit false

theorem mme_cyclic_triple_grading_nonzero_factors
    {K : Type u} [Field K] {T : TensorObj K 3} {t : Nat}
    (G : T.TypeGrading t)
    (rhoX rhoY rhoZ : Fin 3 -> Fin t)
    (h : (mmeCyclicTripleGrading G).blockTensor
      (mmeCyclicTripleGrade rhoX rhoY rhoZ) ≠ 0) :
    G.blockTensor rhoX ≠ 0 ∧
      G.blockTensor rhoY ≠ 0 ∧
      G.blockTensor rhoZ ≠ 0 := by
  sorry
