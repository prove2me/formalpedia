-- Prove2me | Theorems.Thm_mme_permutation_modewise_map_eq
-- name    : mme_permutation_modewise_map_eq
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T04:59:27.965969+00:00
-- url     : https://prove2.me/theorems/b91145ed-aeda-42af-bb47-ec8277da461a
-- title:
--   Modewise linear maps commute with mode reindexing
-- statement:
--   Let $T\in\bigotimes_{i=0}^{d-1}V_i$ be a finite-dimensional tensor over a field, let $f_i:V_i\to V_i$ be linear endomorphisms, and let $\sigma$ permute the modes. Then
--   $$\sigma\!\left((\bigotimes_i f_i)T\right)=(\bigotimes_i f_{\sigma^{-1}(i)})\,\sigma(T).$$
--   The equality is stated for tensor objects with their mode spaces retained. It transports projections and other modewise maps along the same reindexing as the tensor.
-- source:
--   Naturality of tensor mode reindexing under Kronecker products and modewise linear maps.

import Definitions.Def_mme_permutation

open MME PiTensorProduct
universe u
set_option autoImplicit false

theorem mme_permutation_modewise_map_eq {K : Type u} [Field K] {d : ℕ}
    (e : Equiv.Perm (Fin d)) (X : TensorObj K d)
    (f : ∀ i, X.V i →ₗ[K] X.V i) :
    TensorObj.permObj e { X with t := PiTensorProduct.map f X.t } =
      { TensorObj.permObj e X with t :=
        (PiTensorProduct.map (fun i => f (e.symm i))
          (TensorObj.permObj e X).t) } := by sorry
