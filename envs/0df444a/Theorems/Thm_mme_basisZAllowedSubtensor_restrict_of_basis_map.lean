-- Prove2me | Theorems.Thm_mme_basisZAllowedSubtensor_restrict_of_basis_map
-- name    : mme_basisZAllowedSubtensor_restrict_of_basis_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T14:28:39.573278+00:00
-- url     : https://prove2.me/theorems/4803c076-ca59-41d7-946e-b3a0d87d4210
-- title:
--   Basis-compatible tensor restrictions descend to Z-only masks
-- statement:
--   Let $T$ restrict to $U$ through mode maps $f_i$. Fix canonical bases of their $Z$ modes and predicates selecting allowed basis vectors. Suppose every source $Z$-basis vector is either killed by $f_2$ or is sent to a target basis vector, and in the latter case the two allowedness predicates agree. Then the $Z$-only allowed subtensor of $T$ restricts to the $Z$-only allowed subtensor of $U$. The first two mode spaces remain whole throughout. This is the mask-transport principle needed to regroup a literal broken Table-2 copy without duplicating its shared $X/Y$ variables.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Remark 5.1 and Additional Zeroing-Out Step 2; https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_restrict_basisZAllowedSubtensor_of_vanishes
import Theorems.Thm_mme_basisZAllowedSubtensor_projection_certificate
import Definitions.Def_mme_TypeGrading_kron

open MME Module PiTensorProduct

universe u

set_option autoImplicit false

theorem mme_basisZAllowedSubtensor_restrict_of_basis_map
    {K : Type u} [Field K]
    (T U : TensorObj K 3) {ι κ : Type u}
    (bT : Basis ι K (T.V 2)) (bU : Basis κ K (U.V 2))
    (allowedT : ι → Prop) (allowedU : κ → Prop)
    [DecidablePred allowedT] [DecidablePred allowedU]
    (f : ∀ i : Fin 3, T.V i →ₗ[K] U.V i)
    (hmap : PiTensorProduct.map f T.t = U.t)
    (σ : ι → Option κ)
    (hNone : ∀ j, σ j = none → f 2 (bT j) = 0)
    (hSome : ∀ j k, σ j = some k → f 2 (bT j) = bU k)
    (hAllowed : ∀ j k, σ j = some k →
      (allowedT j ↔ allowedU k)) :
    TensorObj.Restrict
      (U.basisZAllowedSubtensor bU allowedU)
      (T.basisZAllowedSubtensor bT allowedT) := by
  sorry
