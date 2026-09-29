-- Prove2me | Theorems.Thm_mme_CW_square_canonical_central202_restrict
-- name    : mme_CW_square_canonical_central202_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T21:25:42.812878+00:00
-- url     : https://prove2.me/theorems/33b20f7a-8a76-45c2-b5f7-a71a00f316ff
-- title:
--   The 202 central field of the canonical CW square
-- statement:
--   In the canonical five-grading of $T_q\otimes T_q$, the 202 central constituent restricts to
--
--   $$
--   T_{202}\ge\langle q^2+2,1,1\rangle.
--   $$
--
--   This is the cyclic rotation of the 022 central field and uses exactly the corresponding block of the same fixed canonical grading.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 265--266, constituent 202 of the squared tensor.

import Definitions.Def_mme_CW_square_canonical_grading
open MME
universe u

theorem mme_CW_square_canonical_central202_restrict
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict (MMObj K (q ^ 2 + 2) 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 2 0 2)) := by sorry
