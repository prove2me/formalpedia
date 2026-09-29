-- Prove2me | Theorems.Thm_mme_CW_square_canonical_central022_restrict
-- name    : mme_CW_square_canonical_central022_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T21:25:38.902718+00:00
-- url     : https://prove2.me/theorems/ccd7ebe7-3583-4578-a103-5a14b85350c0
-- title:
--   The 022 central field of the canonical CW square
-- statement:
--   In the canonical five-grading of $T_q\otimes T_q$, the 022 central constituent restricts to
--
--   $$
--   T_{022}\ge\langle1,1,q^2+2\rangle.
--   $$
--
--   The $q^2$ channels come from pairs of middle coordinates, while the two additional channels come from the two ordered endpoint pairs. This is the first of the three central fields of the standard squared-tensor decomposition.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 265--266, constituent 022 of the squared tensor.

import Definitions.Def_mme_CW_square_canonical_grading
open MME
universe u

theorem mme_CW_square_canonical_central022_restrict
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict (MMObj K 1 1 (q ^ 2 + 2))
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 0 2 2)) := by sorry
