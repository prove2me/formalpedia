-- Prove2me | Theorems.Thm_mme_CW_square_canonical_rect103_301
-- name    : mme_CW_square_canonical_rect103_301
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T21:25:30.506943+00:00
-- url     : https://prove2.me/theorems/22bd94d2-feee-4e0e-ad25-e8730ee38a44
-- title:
--   The 103 and 301 rectangular fields of the canonical CW square
-- statement:
--   For the canonical five-grading of $T_q\otimes T_q$, the next cyclic pair of rectangular constituents each restricts to a matrix-multiplication tensor with long side $2q$:
--
--   $$
--   T_{103}\ge\langle2q,1,1\rangle,\qquad T_{301}\ge\langle2q,1,1\rangle.
--   $$
--
--   These are the cyclic rotations of the 013 and 031 fields, stated directly on the same fixed canonical grading.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 265--266, constituents 103 and 301 of the squared tensor.

import Definitions.Def_mme_CW_square_canonical_grading
open MME
universe u

theorem mme_CW_square_canonical_rect103_301
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict (MMObj K (2 * q) 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 1 0 3)) ∧
    TensorObj.Restrict (MMObj K (2 * q) 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 3 0 1)) := by sorry
