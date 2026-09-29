-- Prove2me | Theorems.Thm_mme_CW_square_canonical_rect013_031
-- name    : mme_CW_square_canonical_rect013_031
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T21:25:25.676082+00:00
-- url     : https://prove2.me/theorems/4b3c5f6e-bde9-4115-97d0-0f743a13210f
-- title:
--   The 013 and 031 rectangular fields of the canonical CW square
-- statement:
--   For the canonical five-grading of $T_q\otimes T_q$, the two rectangular constituents in the first cyclic orientation each restrict to a matrix-multiplication tensor with long side $2q$:
--
--   $$
--   T_{013}\ge\langle1,1,2q\rangle,\qquad T_{031}\ge\langle1,1,2q\rangle.
--   $$
--
--   The two channels of length $q$ arise from the two possible orders of the middle and endpoint coordinates. Both restrictions use blocks of the same fixed canonical grading.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 265--266, constituents 013 and 031 of the squared tensor.

import Definitions.Def_mme_CW_square_canonical_grading
open MME
universe u

theorem mme_CW_square_canonical_rect013_031
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict (MMObj K 1 1 (2 * q))
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 0 1 3)) ∧
    TensorObj.Restrict (MMObj K 1 1 (2 * q))
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 0 3 1)) := by sorry
