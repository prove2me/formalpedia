-- Prove2me | Theorems.Thm_mme_CW_square_canonical_coupled112_restrict
-- name    : mme_CW_square_canonical_coupled112_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T20:34:23.240562+00:00
-- url     : https://prove2.me/theorems/8959341d-b56d-481d-ae7c-504fb8cafe16
-- title:
--   The 112 block is the coupled CW constituent
-- statement:
--   Let $T_q$ be the Coppersmith--Winograd tensor and use the shared canonical five-grading of $T_q\otimes T_q$. The block with grade triple $(1,1,2)$ restricts to the four-sum coupled constituent $C_q$:
--
--   $$
--   C_q \preceq (T_q\otimes T_q)_{112}.
--   $$
--
--   This is the unrotated member of the three-block coupled orbit, and the grading is the same fixed grading used by the complete square-orbit certificate.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 265--266, constituent (d).

import Definitions.Def_mme_CW_square_canonical_grading
import Definitions.Def_mme_permutation
open MME
universe u

theorem mme_CW_square_canonical_coupled112_restrict
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict (coupledObj K q)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 1 1 2)) := by sorry
