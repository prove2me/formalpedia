-- Prove2me | Theorems.Thm_mme_restrict_basisZAllowedSubtensor_of_vanishes
-- name    : mme_restrict_basisZAllowedSubtensor_of_vanishes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T13:23:13.384368+00:00
-- url     : https://prove2.me/theorems/a7d1ab3e-4ef4-48be-8fba-23977e9dd675
-- title:
--   A restriction annihilating disallowed Z words descends to the allowed-word subtensor
-- statement:
--   Let $T$ be a three-mode tensor with a chosen basis $(b_j)$ of its Z space, and let $T_{\mathrm{allow}}$ be the Z-only projection retaining exactly the basis vectors satisfying a predicate. Suppose modewise linear maps restrict $T$ to a tensor $A$. If the Z map annihilates every disallowed basis vector, then those maps factor through the projected source and give a genuine restriction
--
--   $$
--   A\;\le\;T_{\mathrm{allow}}.
--   $$
--
--   This is the linear descent interface used for DWZ restricted splitting: once a coupled component extraction is shown to vanish outside the exact prescribed split histogram, its value witness applies to the literal allowed-word component rather than only to the unrestricted coarse component.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definitions 5.2-5.4 and Section 6.3 restricted splitting (the exact-word projection/factorization used for component tensors); https://arxiv.org/abs/2210.10173

import Mathlib
import Definitions.Def_mme_basis_z_allowed_projection
import Theorems.Thm_mme_basisZAllowed_blockSubtensor_inclusion_tensor

open MME Module PiTensorProduct

universe u

set_option autoImplicit false

theorem mme_restrict_basisZAllowedSubtensor_of_vanishes
    {K : Type u} [Field K]
    (T A : TensorObj K 3) {ι : Type u}
    (bZ : Basis ι K (T.V 2)) (allowed : ι → Prop)
    [DecidablePred allowed]
    (f : ∀ i, T.V i →ₗ[K] A.V i)
    (hmap : PiTensorProduct.map f T.t = A.t)
    (hvanish : ∀ j, ¬ allowed j → f 2 (bZ j) = 0) :
    TensorObj.Restrict A (T.basisZAllowedSubtensor bZ allowed) := by
  sorry
