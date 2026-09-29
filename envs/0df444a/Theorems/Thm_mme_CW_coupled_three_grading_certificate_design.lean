-- Prove2me | Theorems.Thm_mme_CW_coupled_three_grading_certificate_design
-- name    : mme_CW_coupled_three_grading_certificate_design
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T03:56:05.227033+00:00
-- url     : https://prove2.me/theorems/5a63647b-f4be-4ccc-97dc-f1b9b7435061
-- title:
--   The coupled Coppersmith--Winograd tensor has its concrete four-block grading
-- statement:
--   For every field $K$ and natural number $q$, the coupled four-sum tensor $D_q$ has a three-class grading whose support is exactly contained in
--
--   $$
--   \{(0,0,0),(1,1,1),(0,1,2),(1,0,2)\}.
--   $$
--
--   The diagonal blocks $(0,0,0)$ and $(1,1,1)$ each restrict to $\langle1,q,1\rangle$, while the crossed blocks $(0,1,2)$ and $(1,0,2)$ each restrict to $\langle q,1,q\rangle$. This is the concrete tensor certificate needed to apply the abstract induced-star zeroing lemma to the explicit coupled Coppersmith--Winograd tensor.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), the four displayed coupled summands on journal p. 270; https://doi.org/10.1016/S0747-7171(08)80013-2.

import Definitions.Def_mme_CW_q6_primary_hash_family
import Definitions.Def_coupledQ6OrientedSurvivor
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_block_subtensor

open MME

universe u

theorem mme_CW_coupled_three_grading_certificate_design
    {K : Type u} [Field K] (q : ℕ) :
    ∃ grading : (coupledObj K q).TypeGrading 3,
      (∀ σ : Fin 3 → Fin 3,
        σ ≠ ![0, 0, 0] → σ ≠ ![1, 1, 1] →
        σ ≠ ![0, 1, 2] → σ ≠ ![1, 0, 2] →
        grading.blockTensor σ = 0) ∧
      TensorObj.Restrict (MMObj K 1 q 1)
        (grading.blockSubtensor ![0, 0, 0]) ∧
      TensorObj.Restrict (MMObj K 1 q 1)
        (grading.blockSubtensor ![1, 1, 1]) ∧
      TensorObj.Restrict (MMObj K q 1 q)
        (grading.blockSubtensor ![0, 1, 2]) ∧
      TensorObj.Restrict (MMObj K q 1 q)
        (grading.blockSubtensor ![1, 0, 2]) := by
  sorry
