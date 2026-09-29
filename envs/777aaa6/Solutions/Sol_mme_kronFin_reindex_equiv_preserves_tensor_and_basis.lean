-- Prove2me | solution 1 for mme_kronFin_reindex_equiv_preserves_tensor_and_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T07:56:07.938861+00:00
-- url     : https://prove2.me/submissions/fbb917ba-568c-48ba-bb08-c4b42f3f2132

import Theorems.Thm_mme_kronFin_perm_preserves_tensor_and_basis

open MME Module PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
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
  have hmn : m = n := by
    simpa using Fintype.card_congr e
  subst n
  obtain ⟨q, hq⟩ : ∃ q, m = q + 2 := by
    exact ⟨m - 2, by omega⟩
  subst m
  exact mme_kronFin_perm_preserves_tensor_and_basis T e
