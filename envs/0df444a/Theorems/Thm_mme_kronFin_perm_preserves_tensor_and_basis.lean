-- Prove2me | Theorems.Thm_mme_kronFin_perm_preserves_tensor_and_basis
-- name    : mme_kronFin_perm_preserves_tensor_and_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T20:28:11.31909+00:00
-- url     : https://prove2.me/theorems/d97987fb-44b1-4b61-95f5-e55fb7dc2a86
-- title:
--   Every heterogeneous finite Kronecker permutation preserves the tensor with exact basis action
-- statement:
--   For any permutation $e$ of at least two positions in a heterogeneous finite Kronecker product, there are modewise linear equivalences from the factor family $T\circ e$ to the original factor family. These maps preserve the literal tensor and act on every dependent product-basis word by the canonical dependent reindexing along $e$. This supplies the exact factor-regrouping map required when retained source positions are gathered by their fifteen Table-2 component types.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.2 and Claim 5.9 (component-position regrouping); https://arxiv.org/abs/2210.10173

import Theorems.Thm_mme_kronFin_adjacent_swap_equiv_preserves_tensor_and_basis
import Mathlib.GroupTheory.Perm.Sign

open MME Module PiTensorProduct

universe u

set_option autoImplicit false

theorem mme_kronFin_perm_preserves_tensor_and_basis
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin (n + 2) → TensorObj K d)
    (e : Equiv.Perm (Fin (n + 2))) :
    ∃ F : ∀ i : Fin d,
        (TensorObj.kronFin (n + 2) (fun r ↦ T (e r))).V i ≃ₗ[K]
          (TensorObj.kronFin (n + 2) T).V i,
      PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
          (TensorObj.kronFin (n + 2) (fun r ↦ T (e r))).t =
        (TensorObj.kronFin (n + 2) T).t ∧
      ∀ (i : Fin d) (index : Fin (n + 2) → Type u)
        (b : ∀ r, Basis (index r) K ((T r).V i))
        (w : ∀ r, index (e r)),
        F i
            (TensorObj.kronFinModePiBasis (n + 2)
              (fun r ↦ T (e r)) i (fun r ↦ b (e r)) w) =
          TensorObj.kronFinModePiBasis (n + 2) T i b
            (Equiv.piCongrLeft index e w) := by
  sorry
