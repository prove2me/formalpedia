-- Prove2me | Theorems.Thm_mme_CW_coupled_three_grading_isomorphism_certificate
-- name    : mme_CW_coupled_three_grading_isomorphism_certificate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T04:44:29.90553+00:00
-- url     : https://prove2.me/theorems/3780d414-4788-4f00-b558-7a5f42aa7714
-- title:
--   Exact four-block grading and isomorphism certificate for the coupled CW tensor
-- statement:
--   For every field $K$ and integer $q$, the coupled Coppersmith--Winograd constituent admits a three-grade coordinate decomposition whose only nonzero blocks have grades $(0,0,0)$, $(1,1,1)$, $(0,1,2)$, and $(1,0,2)$. The first two blocks are isomorphic to $\langle 1,q,1\rangle$, while the last two are isomorphic to $\langle q,1,q\rangle$.
--
--   The isomorphism assertion is two-sided. In particular, it records the transpose-sensitive coordinate identification of the $(1,0,2)$ block and is strong enough to build genuine C-tensor component certificates after hash zeroing.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), coupled constituent on journal pp. 266 and 270.

import Definitions.Def_mme_CW_square_canonical_grading
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_block_subtensor
import Definitions.Def_mme_tensor_quotient
import Mathlib.Tactic

open MME PiTensorProduct BigOperators DirectSum Module

universe u

theorem mme_CW_coupled_three_grading_isomorphism_certificate
    {K : Type u} [Field K] (q : ℕ) :
    ∃ grading : (coupledObj K q).TypeGrading 3,
      (∀ sigma : Fin 3 → Fin 3,
        sigma ≠ ![0, 0, 0] → sigma ≠ ![1, 1, 1] →
        sigma ≠ ![0, 1, 2] → sigma ≠ ![1, 0, 2] →
        grading.blockTensor sigma = 0) ∧
      TensorObj.Isomorphic (MMObj K 1 q 1)
        (grading.blockSubtensor ![0, 0, 0]) ∧
      TensorObj.Isomorphic (MMObj K 1 q 1)
        (grading.blockSubtensor ![1, 1, 1]) ∧
      TensorObj.Isomorphic (MMObj K q 1 q)
        (grading.blockSubtensor ![0, 1, 2]) ∧
      TensorObj.Isomorphic (MMObj K q 1 q)
        (grading.blockSubtensor ![1, 0, 2]) := by
  sorry
