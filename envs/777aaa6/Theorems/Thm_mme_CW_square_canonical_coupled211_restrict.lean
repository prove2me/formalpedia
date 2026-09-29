-- Prove2me | Theorems.Thm_mme_CW_square_canonical_coupled211_restrict
-- name    : mme_CW_square_canonical_coupled211_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T20:34:38.55153+00:00
-- url     : https://prove2.me/theorems/ccc4c809-5a74-47dc-af45-bbda377ad8e4
-- title:
--   The 211 block is the first cyclic coupled CW constituent
-- statement:
--   Let $T_q$ be the Coppersmith--Winograd tensor and use the shared canonical five-grading of $T_q\otimes T_q$. The block with grade triple $(2,1,1)$ restricts to the first cyclic rotation $\sigma C_q$ of the four-sum coupled constituent $C_q$:
--
--   $$
--   \sigma C_q \preceq (T_q\otimes T_q)_{211}.
--   $$
--
--   This is the first rotated member of the three-block coupled orbit, using exactly the grading fixed by the complete square-orbit certificate.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 265--266, constituent (d) and its cyclic grade orbit.

import Definitions.Def_mme_CW_square_canonical_grading
import Definitions.Def_mme_permutation
open MME
universe u

theorem mme_CW_square_canonical_coupled211_restrict
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict
      (TensorObj.permObj cyclicPerm (coupledObj K q))
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 2 1 1)) := by sorry
