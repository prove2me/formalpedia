-- Prove2me | Theorems.Thm_mme_dwz_basisLabelProjection_singleton_tensor_transport
-- name    : mme_dwz_basisLabelProjection_singleton_tensor_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T11:01:55.331773+00:00
-- url     : https://prove2.me/theorems/be758d49-7721-45fd-871e-b341e24a9df9
-- title:
--   A common basis shuffle transports each singleton labelled tensor block
-- statement:
--   Let $X$ be a trilinear tensor with a chosen basis of its third mode, and let each basis vector carry a label in a finite block set. Suppose the modewise automorphism $F_0\otimes F_1\otimes F_2$ preserves $X$, while $F_2$ permutes the chosen basis and moves its labels by a permutation $\pi$. If $P_z$ is the diagonal third-mode projection onto basis vectors labelled by $z$, then
--
--   $$
--   (F_0\otimes F_1\otimes F_2)(\operatorname{id}\otimes\operatorname{id}\otimes P_z)(X)
--   =
--   (\operatorname{id}\otimes\operatorname{id}\otimes P_{\pi(z)})(X).
--   $$
--
--   Thus every singleton labelled contribution is transported exactly, rather than merely up to tensor isomorphism. This is the map-level bridge used to move each nonhole useful block of a broken DWZ standard tensor through the common grouped shuffle.
--
--   **Formalization Note** The basis permutation is supplied pointwise, including the equality of both the transformed basis vector and its moved label.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.7 and Claims 5.8--5.10, especially the common tensor shuffle in the proof of Claim 5.9; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_basis_label_projection

open MME Module
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_basisLabelProjection_singleton_tensor_transport
    {K : Type u} [Field K]
    (X : TensorObj K 3) {ι β : Type u} [DecidableEq β]
    (b : Basis ι K (X.V 2)) (label : ι → β)
    (F : ∀ i, X.V i ≃ₗ[K] X.V i) (move : Equiv.Perm β)
    (hTensor :
      PiTensorProduct.map (fun i ↦ (F i).toLinearMap) X.t = X.t)
    (hF : ∀ x, ∃ y,
      F 2 (b x) = b y ∧ label y = move (label x))
    (block : β) :
    PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
        (PiTensorProduct.map
          (Function.update (fun _ ↦ LinearMap.id) 2
            (basisLabelProjection b label {block})) X.t) =
      PiTensorProduct.map
        (Function.update (fun _ ↦ LinearMap.id) 2
          (basisLabelProjection b label {move block})) X.t := by
  sorry
