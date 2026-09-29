-- Prove2me | Theorems.Thm_mme_CW_square_canonical_coupled121_restrict
-- name    : mme_CW_square_canonical_coupled121_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T20:27:20.000701+00:00
-- url     : https://prove2.me/theorems/ff07c721-62db-4e68-af4c-ed803bd3c2e8
-- title:
--   The 121 block is the second cyclic coupled CW constituent
-- statement:
--   Let $T_q$ be the Coppersmith--Winograd tensor and use the shared canonical five-grading of $T_q\otimes T_q$.  The block with grade triple $(1,2,1)$ restricts to the second cyclic rotation $\sigma^2 C_q$ of the four-sum coupled constituent $C_q$.  Equivalently,
--
--   $$
--   \sigma^2 C_q\preceq (T_q\otimes T_q)_{121}.
--   $$
--
--   The statement uses the same fixed grading as every other orbit block; it does not choose a new existential grading.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 265--266, constituent (d) and its cyclic grade orbit.

import Definitions.Def_mme_CW_square_canonical_grading
import Definitions.Def_mme_permutation
open MME
universe u

theorem mme_CW_square_canonical_coupled121_restrict
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q))
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 1 2 1)) := by sorry
