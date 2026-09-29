-- Prove2me | Theorems.Thm_mme_kronFin_reindex_equiv_preserves_tensor_and_basis
-- name    : mme_kronFin_reindex_equiv_preserves_tensor_and_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T07:36:34.804332+00:00
-- url     : https://prove2.me/theorems/6cf9e046-0a38-4ca4-abd5-3958ba776a3f
-- title:
--   Exact coordinate semantics for heterogeneous Kronecker reindexing
-- statement:
--   Let two finite position sets have the same size, at least two, and let e identify the reordered positions with the target positions. For any heterogeneous family of tensors, there are modewise linear equivalences from the ordered product of the reindexed family to the original ordered product. They preserve the literal tensor and send every dependent product-basis word to the exact word transported along e. This is the coordinate-strengthened reindexing needed to turn source-order DWZ retained words into consecutive Table-2 component fibers.
-- source:
--   Duan–Wu–Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Section 6 and Table 2; finite factor regrouping used in the Prove2Me 2.3747 mission.

import Theorems.Thm_mme_kronFin_perm_preserves_tensor_and_basis

open MME Module PiTensorProduct

universe u

set_option autoImplicit false

theorem mme_kronFin_reindex_equiv_preserves_tensor_and_basis
    {K : Type u} [Field K] {d m n : ℕ} (hm : 2 ≤ m)
    (T : Fin n → TensorObj K d) (e : Fin m ≃ Fin n) :
    ∃ F : ∀ i : Fin d,
        (TensorObj.kronFin m (fun r ↦ T (e r))).V i ≃ₗ[K]
          (TensorObj.kronFin n T).V i,
      PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
          (TensorObj.kronFin m (fun r ↦ T (e r))).t =
        (TensorObj.kronFin n T).t ∧
      ∀ (i : Fin d) (index : Fin n → Type u)
        (b : ∀ r, Basis (index r) K ((T r).V i))
        (w : ∀ r, index (e r)),
        F i
            (TensorObj.kronFinModePiBasis m
              (fun r ↦ T (e r)) i (fun r ↦ b (e r)) w) =
          TensorObj.kronFinModePiBasis n T i b
            (Equiv.piCongrLeft index e w) := by
  sorry
