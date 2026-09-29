-- Prove2me | Theorems.Thm_mme_basis_preserving_restriction_mask_descent
-- name    : mme_basis_preserving_restriction_mask_descent
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T05:02:26.564069+00:00
-- url     : https://prove2.me/theorems/9cec27af-ae12-418f-ab51-9010aefd4dfb
-- title:
--   Basis-preserving restrictions descend through coordinate masks
-- statement:
--   Let $X$ and $Y$ be finite-dimensional tensors of order $d$ over a field, and let modewise linear maps $F_i$ take $X$ to $Y$. Suppose $F_i$ sends each chosen source basis vector $b_{i,a}$ to the equally indexed target basis vector $c_{i,a}$. Choose any predicate $P_i$ on the common index set in each mode. Let $p_i$ and $q_i$ be the respective basis projections retaining precisely the indices satisfying $P_i$. Then
--   $$(\bigotimes_i q_i)Y\preceq(\bigotimes_i p_i)X.$$
--   The predicates may describe arbitrary sets of tensor-power words. Thus the same allowed-word conditions can be retained while transporting a tensor restriction.
-- source:
--   Naturality of tensor mode reindexing under Kronecker products and modewise linear maps.

import Definitions.Def_mme_tensor_rank
import Mathlib.LinearAlgebra.Basis.Defs

open MME Module PiTensorProduct
universe u
set_option autoImplicit false

theorem mme_basis_preserving_restriction_mask_descent
    {K : Type u} [Field K] {d : ℕ} {X Y : TensorObj K d}
    (F : ∀ i, X.V i →ₗ[K] Y.V i)
    (hF : PiTensorProduct.map F X.t = Y.t)
    {ι : Fin d → Type u}
    (b : ∀ i, Basis (ι i) K (X.V i)) (c : ∀ i, Basis (ι i) K (Y.V i))
    (hb : ∀ i a, F i (b i a) = c i a)
    (keep : ∀ i, ι i → Prop) [∀ i, DecidablePred (keep i)] :
    let p : ∀ i, X.V i →ₗ[K] X.V i :=
      fun i => (b i).constr K (fun a => if keep i a then b i a else 0)
    let q : ∀ i, Y.V i →ₗ[K] Y.V i :=
      fun i => (c i).constr K (fun a => if keep i a then c i a else 0)
    TensorObj.Restrict { Y with t := PiTensorProduct.map q Y.t }
      { X with t := PiTensorProduct.map p X.t } := by sorry
