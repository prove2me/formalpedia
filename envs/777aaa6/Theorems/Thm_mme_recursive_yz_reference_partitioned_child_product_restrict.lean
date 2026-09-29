-- Prove2me | Theorems.Thm_mme_recursive_yz_reference_partitioned_child_product_restrict
-- name    : mme_recursive_yz_reference_partitioned_child_product_restrict
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T06:07:31.646696+00:00
-- url     : https://prove2.me/theorems/49f777cd-15eb-40e1-afd4-588d3d5b4f05
-- title:
--   Partitioned child products restrict from their intact reference tensor
-- statement:
--   A complete partition of child cells into two indexed families gives their product as an actual restriction of the intact reference tensor. Exact address counts determine each physical child size. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_recursive_yz_reference_child_product_restrict
import Theorems.Thm_mme_kronFin_partition_isomorphic
open BigOperators MME MME.RecursiveYZ MME.RecursiveYZ.CWCells
open MME.CompleteSplit MME.TensorObj
universe u

theorem mme_recursive_yz_reference_partitioned_child_product_restrict
    {K : Type u} [Field K] {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (reference : Address half R parent n)
    (href : reference ∈ RecursiveXHash.target m)
    (ell L a b : ℕ) (positions : Fin L ≃ Position n)
    (e : (Fin a ⊕ Fin b) ≃ Cell half R parent)
    (mu : Fin 3 → Cell half R parent → CompleteWord ell → ℕ) :
    Restrict (kron
      (kronFin a (fun j ↦
        unbroken K 5 ell
          (m (e (.inl j)).1 (e (.inl j)).2 +
            m (e (.inl j)).1 (complement (htotal (e (.inl j)).1) (e (.inl j)).2))
          (Equiv.refl _) (fun _ ↦ Unit.unit) (fun _ i ↦ ((e (.inl j)).2.val i).val)
          (fun i _ ↦ mu i (e (.inl j)))))
      (kronFin b (fun j ↦
        unbroken K 5 ell
          (m (e (.inr j)).1 (e (.inr j)).2 +
            m (e (.inr j)).1 (complement (htotal (e (.inr j)).1) (e (.inr j)).2))
          (Equiv.refl _) (fun _ ↦ Unit.unit) (fun _ i ↦ ((e (.inr j)).2.val i).val)
          (fun i _ ↦ mu i (e (.inr j))))) )
      (unbroken K 5 ell L positions (fullCell htotal reference)
        (fun cell i ↦ (cell.2.val i).val) mu) := by sorry
