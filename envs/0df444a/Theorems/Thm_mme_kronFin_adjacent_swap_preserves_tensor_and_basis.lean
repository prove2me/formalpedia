-- Prove2me | Theorems.Thm_mme_kronFin_adjacent_swap_preserves_tensor_and_basis
-- name    : mme_kronFin_adjacent_swap_preserves_tensor_and_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T19:44:23.210432+00:00
-- url     : https://prove2.me/theorems/4c08d058-6aa1-408e-9c03-92e1fc2d47ba
-- title:
--   Adjacent heterogeneous Kronecker swap preserves the tensor and its dependent product basis
-- statement:
--   Let T_0,...,T_{n+1} be heterogeneous tensors and exchange the adjacent factors at positions j and j+1. There are modewise linear equivalences from the exchanged ordered product to the original ordered product that preserve the literal tensor. For any heterogeneous dependent choice of factor bases, the same equivalences send every product-basis vector to the vector obtained by restoring the two labels to their original positions. Thus this is an exact coordinate-level symmetry, not only an equality in an isomorphism quotient.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.2 and Claim 5.9 (component-position regrouping); https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_kronFin_adjacent_swap_data

open MME PiTensorProduct Module

universe u

set_option autoImplicit false

theorem mme_kronFin_adjacent_swap_preserves_tensor_and_basis
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin (n + 2) → TensorObj K d) (j : Fin (n + 1)) :
    ∃ F : ∀ i : Fin d,
        (TensorObj.kronFin (n + 2)
          (TensorObj.kronFinAdjacentSwapFamily T j)).V i ≃ₗ[K]
        (TensorObj.kronFin (n + 2) T).V i,
      PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
          (TensorObj.kronFin (n + 2)
            (TensorObj.kronFinAdjacentSwapFamily T j)).t =
        (TensorObj.kronFin (n + 2) T).t ∧
      ∀ (i : Fin d) {index : Fin (n + 2) → Type u}
          (b : ∀ r, Basis (index r) K ((T r).V i))
          (w : ∀ r, TensorObj.kronFinAdjacentSwapIndex index j r),
        F i
            (TensorObj.kronFinModePiBasis (n + 2)
              (TensorObj.kronFinAdjacentSwapFamily T j) i
              (TensorObj.kronFinAdjacentSwapBasis T j i b) w) =
          TensorObj.kronFinModePiBasis (n + 2) T i b
            (TensorObj.kronFinAdjacentUnswapWord j w) := by
  sorry
