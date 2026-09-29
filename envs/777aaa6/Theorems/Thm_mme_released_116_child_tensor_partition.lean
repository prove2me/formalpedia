-- Prove2me | Theorems.Thm_mme_released_116_child_tensor_partition
-- name    : mme_released_116_child_tensor_partition
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T01:27:25.537711+00:00
-- url     : https://prove2.me/theorems/d1e835f3-a651-4f10-a6ab-6f9adfa82a19
-- title:
--   Released child tensor partitions into eighteen boundary and six interior factors
-- statement:
--   There is an equivalence from eighteen boundary indices plus six interior indices to the full released 116 child cell index. Every boundary factor has a zero mode, and interior index r is exactly region r with shape 112. For any enumeration of all twenty-four cells and any field-valued tensor family on the cells, its full finite product is isomorphic to the Kronecker product of these boundary and interior products. Every cell occurs once.
-- source:
--   Kernel-checked released split enumeration and finite tensor product reindexing.

import Definitions.Def_mme_released_116_integer_profiles
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Theorems.Thm_mme_toQ_kronFin
open MME MME.RecursiveYZ MME.Released116
open MME BigOperators
set_option autoImplicit false
universe u

theorem mme_released_116_child_tensor_partition :
    ∃ e : (Fin 18 ⊕ Fin 6) ≃ Cell 4 6 parent,
      (∀ i : Fin 18, ∃ z : Fin 3, ((e (.inl i)).2.val z).val = 0) ∧
      (∀ r : Fin 6, e (.inr r) = ⟨r, ⟨![1, 1, 2], by
        change _ ∧ ∀ i, _ ≤ (![1, 1, 6] : Fin 3 → ℕ) i
        decide⟩⟩) ∧
      ∀ (d : Fin 24 ≃ Cell 4 6 parent) (K : Type u) [Field K]
        (T : Cell 4 6 parent → TensorObj K 3),
        TensorObj.Isomorphic (TensorObj.kronFin 24 (fun i ↦ T (d i)))
          (TensorObj.kron
            (TensorObj.kronFin 18 (fun i ↦ T (e (.inl i))))
            (TensorObj.kronFin 6 (fun r ↦ T ⟨r, ⟨![1, 1, 2], by
              change _ ∧ ∀ i, _ ≤ (![1, 1, 6] : Fin 3 → ℕ) i
              decide⟩⟩))) := by sorry
