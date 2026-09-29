-- Prove2me | Theorems.Thm_mme_recursive_yz_scaled_reference_partitioned_child_product_restrict
-- name    : mme_recursive_yz_scaled_reference_partitioned_child_product_restrict
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T06:14:33.730789+00:00
-- url     : https://prove2.me/theorems/0b1a0814-0dc1-4ed8-8a14-2ab492c6f02b
-- title:
--   Replicated child products restrict at their normalized physical sizes
-- statement:
--   A common replication factor can be pulled outside each child size in the partitioned reference restriction, including zero replication and empty cells. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_recursive_yz_reference_partitioned_child_product_restrict
open BigOperators MME MME.RecursiveYZ MME.RecursiveYZ.CWCells
open MME.CompleteSplit MME.TensorObj
universe u

theorem mme_recursive_yz_scaled_reference_partitioned_child_product_restrict
    {K : Type u} [Field K] {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (k : ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (reference : Address half R parent n)
    (href : reference ∈ RecursiveXHash.target (fun r c => k * m r c))
    (ell L a b : ℕ) (positions : Fin L ≃ Position n)
    (e : (Fin a ⊕ Fin b) ≃ Cell half R parent)
    (mu : Fin 3 → Cell half R parent → CompleteWord ell → ℕ) :
    Restrict (kron
      (kronFin a (fun j ↦
        unbroken K 5 ell
          (k * (m (e (.inl j)).1 (e (.inl j)).2 +
            m (e (.inl j)).1 (complement (htotal (e (.inl j)).1) (e (.inl j)).2)))
          (Equiv.refl _) (fun _ ↦ Unit.unit) (fun _ i ↦ ((e (.inl j)).2.val i).val)
          (fun i _ ↦ mu i (e (.inl j)))))
      (kronFin b (fun j ↦
        unbroken K 5 ell
          (k * (m (e (.inr j)).1 (e (.inr j)).2 +
            m (e (.inr j)).1 (complement (htotal (e (.inr j)).1) (e (.inr j)).2)))
          (Equiv.refl _) (fun _ ↦ Unit.unit) (fun _ i ↦ ((e (.inr j)).2.val i).val)
          (fun i _ ↦ mu i (e (.inr j))))) )
      (unbroken K 5 ell L positions (fullCell htotal reference)
        (fun cell i ↦ (cell.2.val i).val) mu) := by sorry
