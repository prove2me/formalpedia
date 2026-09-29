-- Prove2me | Theorems.Thm_mme_dwz_basisLabelProjection_singleton_tensor_transport_poly
-- name    : mme_dwz_basisLabelProjection_singleton_tensor_transport_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T11:19:49.602382+00:00
-- url     : https://prove2.me/theorems/89abbb75-b96e-45c3-83f7-aa7e85411c3e
-- title:
--   Universe-polymorphic transport of singleton labelled tensor blocks
-- statement:
--   Let $X$ be a trilinear tensor with a chosen basis of its third mode, whose basis vectors carry labels in an arbitrary type. Suppose $F_0\otimes F_1\otimes F_2$ preserves $X$, and $F_2$ permutes the basis while moving labels by a permutation $\pi$. If $P_z$ projects onto the basis vectors labelled by $z$, then
--
--   $$
--   (F_0\otimes F_1\otimes F_2)(\operatorname{id}\otimes\operatorname{id}\otimes P_z)(X)
--   =
--   (\operatorname{id}\otimes\operatorname{id}\otimes P_{\pi(z)})(X).
--   $$
--
--   This is the exact singleton-block transport needed when a common DWZ grouped shuffle acts on every nonhole summand of a broken standard tensor.
--
--   **Formalization Note** The scalar field, basis-index type, and label type may inhabit independent universes; the latter is essential when finite combinatorial block labels are attached to a tensor over a universe-polymorphic field.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.7 and Claims 5.8--5.10, especially the common tensor shuffle in the proof of Claim 5.9; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_basis_label_projection

open MME Module
open MME.DWZComponentRestriction

universe u v w

set_option autoImplicit false

theorem mme_dwz_basisLabelProjection_singleton_tensor_transport_poly
    {K : Type u} [Field K]
    (X : TensorObj K 3) {ι : Type v} {β : Type w} [DecidableEq β]
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
