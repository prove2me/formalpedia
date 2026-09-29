-- Prove2me | Theorems.Thm_mme_CW_square_canonical_central220_restrict
-- name    : mme_CW_square_canonical_central220_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T21:25:46.85229+00:00
-- url     : https://prove2.me/theorems/23bbd388-c24f-4e73-a9fc-d41be42a2756
-- title:
--   The 220 central field of the canonical CW square
-- statement:
--   In the canonical five-grading of $T_q\otimes T_q$, the 220 central constituent restricts to
--
--   $$
--   T_{220}\ge\langle1,q^2+2,1\rangle.
--   $$
--
--   This is the final cyclic rotation of the central field and completes the three $q^2+2$ constituents on the same fixed grading.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 265--266, constituent 220 of the squared tensor.

import Definitions.Def_mme_CW_square_canonical_grading
open MME
universe u

theorem mme_CW_square_canonical_central220_restrict
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict (MMObj K 1 (q ^ 2 + 2) 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 2 2 0)) := by sorry
