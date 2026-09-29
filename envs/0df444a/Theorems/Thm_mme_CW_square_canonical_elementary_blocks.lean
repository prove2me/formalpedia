-- Prove2me | Theorems.Thm_mme_CW_square_canonical_elementary_blocks
-- name    : mme_CW_square_canonical_elementary_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T20:35:35.657259+00:00
-- url     : https://prove2.me/theorems/5436e5fa-e2d7-4be2-90b8-d45cdf0fd036
-- title:
--   The thirteen elementary fields of the canonical CW-square grading certificate
-- statement:
--   Fix the canonical five-grading of the square $T_q\otimes T_q$ of the Coppersmith--Winograd tensor. This theorem packages the thirteen elementary fields needed by the orbit certificate: vanishing of every block whose three grades do not sum to four, the three scalar blocks, the six rectangular matrix-multiplication blocks, and the three central matrix-multiplication blocks. In the notation of CW90 these are
--
--   $$
--   004,040,400;\qquad 013,031,103,301,130,310;\qquad 022,202,220.
--   $$
--
--   Every restriction is taken from a block of the same fixed public grading; no new grading is chosen.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 265--266, decomposition of the square into fifteen grade-sum-four constituents.

import Definitions.Def_mme_CW_square_canonical_grading
import Definitions.Def_mme_permutation
open MME
universe u

theorem mme_CW_square_canonical_elementary_blocks
    {K : Type u} [Field K] (q : ℕ) :
    (∀ I J L : Fin 5, I.val + J.val + L.val ≠ 4 →
      (cwSquareCanonicalGrading K q).blockTensor
        (cwSquareBlockType I J L) = 0) ∧
    TensorObj.Restrict (MMObj K 1 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 0 0 4)) ∧
    TensorObj.Restrict (MMObj K 1 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 0 4 0)) ∧
    TensorObj.Restrict (MMObj K 1 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 4 0 0)) ∧
    TensorObj.Restrict (MMObj K 1 1 (2 * q))
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 0 1 3)) ∧
    TensorObj.Restrict (MMObj K 1 1 (2 * q))
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 0 3 1)) ∧
    TensorObj.Restrict (MMObj K (2 * q) 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 1 0 3)) ∧
    TensorObj.Restrict (MMObj K (2 * q) 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 3 0 1)) ∧
    TensorObj.Restrict (MMObj K 1 (2 * q) 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 1 3 0)) ∧
    TensorObj.Restrict (MMObj K 1 (2 * q) 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 3 1 0)) ∧
    TensorObj.Restrict (MMObj K 1 1 (q ^ 2 + 2))
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 0 2 2)) ∧
    TensorObj.Restrict (MMObj K (q ^ 2 + 2) 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 2 0 2)) ∧
    TensorObj.Restrict (MMObj K 1 (q ^ 2 + 2) 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 2 2 0)) := by sorry
