-- Prove2me | Theorems.Thm_mme_tensorProduct_basis_filter_absorption
-- name    : mme_tensorProduct_basis_filter_absorption
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T11:16:26.378508+00:00
-- url     : https://prove2.me/theorems/b9fbf861-75a1-4f61-b568-19b0b9b1e6b2
-- title:
--   Product-basis vanishing implies absorption of two basis projectors
-- statement:
--   Let $V$ and $W$ have chosen bases, with specified subsets of allowed basis indices. Let $P_V$ and $P_W$ be the coordinate projectors onto the spans of the allowed basis vectors. If a linear map $f:V\otimes W\to U$ annihilates every product basis vector for which either factor is forbidden, then
--
--   $$f\circ(P_V\otimes P_W)=f.$$
--
--   This converts slotwise vanishing on forbidden paired words into the projector-absorption equation required for exact descent from an ambient paired tensor to its allowed-word source.
-- source:
--   Elementary tensor-product linear algebra; paired basis-projection descent in laser-method tensor restrictions.

import Mathlib.LinearAlgebra.TensorProduct.Basis

open Module TensorProduct

universe u

set_option autoImplicit false

theorem mme_tensorProduct_basis_filter_absorption
    {K : Type u} [Field K]
    {V W U : Type u}
    [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    [AddCommGroup U] [Module K U]
    {iota kappa : Type u}
    (bV : Basis iota K V) (bW : Basis kappa K W)
    (allowedV : iota → Prop) (allowedW : kappa → Prop)
    [DecidablePred allowedV] [DecidablePred allowedW]
    (f : (V ⊗[K] W) →ₗ[K] U)
    (hvanish : ∀ (i : iota) (j : kappa),
      ¬ allowedV i ∨ ¬ allowedW j →
        f (bV i ⊗ₜ[K] bW j) = 0) :
    f.comp (TensorProduct.map
      (bV.constr K (fun i ↦ if allowedV i then bV i else 0))
      (bW.constr K (fun j ↦ if allowedW j then bW j else 0))) = f := by
  sorry
