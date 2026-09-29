-- Prove2me | Theorems.Thm_mme_CW_square_canonical_rect130_310
-- name    : mme_CW_square_canonical_rect130_310
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T21:25:35.317617+00:00
-- url     : https://prove2.me/theorems/2e6efad8-4eb0-4737-a43c-e202074314de
-- title:
--   The 130 and 310 rectangular fields of the canonical CW square
-- statement:
--   For the canonical five-grading of $T_q\otimes T_q$, the final cyclic pair of rectangular constituents each restricts to a matrix-multiplication tensor with long side $2q$:
--
--   $$
--   T_{130}\ge\langle1,2q,1\rangle,\qquad T_{310}\ge\langle1,2q,1\rangle.
--   $$
--
--   Together with the other two rectangular pairs, these give the six rectangular fields in the standard fifteen-constituent decomposition, all on one fixed grading.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 265--266, constituents 130 and 310 of the squared tensor.

import Definitions.Def_mme_CW_square_canonical_grading
open MME
universe u

theorem mme_CW_square_canonical_rect130_310
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict (MMObj K 1 (2 * q) 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 1 3 0)) ∧
    TensorObj.Restrict (MMObj K 1 (2 * q) 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 3 1 0)) := by sorry
