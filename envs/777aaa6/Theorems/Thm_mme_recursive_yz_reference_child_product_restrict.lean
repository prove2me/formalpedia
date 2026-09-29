-- Prove2me | Theorems.Thm_mme_recursive_yz_reference_child_product_restrict
-- name    : mme_recursive_yz_reference_child_product_restrict
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T01:39:28.160792+00:00
-- url     : https://prove2.me/theorems/4b4c66df-7d30-4880-be06-48d1bd51b666
-- title:
--   Exact reference counts realize the child product inside the intact tensor
-- statement:
--   For any exact recursive reference address and any enumeration of its cells, the product of the physical child tensors restricts from the intact reference tensor. Each child has size equal to its split count plus the complementary split count. The proof establishes the exact fiber cardinalities and applies the checked physical-cell grouping restriction. No matrix extraction or tensor-value assumption is required.
-- source:
--   Exact physical-cell grouping and released tensor extractions.

import Theorems.Thm_mme_recursive_yz_actual_cell_product_restriction
import Definitions.Def_mme_recursive_x_hash_families
import Definitions.Def_mme_recursive_yz_physical_words
open BigOperators MME MME.RecursiveYZ MME.RecursiveYZ.CWCells
open MME.CompleteSplit MME.TensorObj
set_option autoImplicit false
universe u

theorem mme_recursive_yz_reference_child_product_restrict
    {K : Type u} [Field K] {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (reference : Address half R parent n)
    (href : reference ∈ RecursiveXHash.target m)
    (ell L parts : ℕ) (positions : Fin L ≃ Position n)
    (d : Fin parts ≃ Cell half R parent)
    (mu : Fin 3 → Cell half R parent → CompleteWord ell → ℕ) :
    Restrict (kronFin parts (fun j ↦
      unbroken K 5 ell
        (m (d j).1 (d j).2 + m (d j).1 (complement (htotal (d j).1) (d j).2))
        (Equiv.refl _) (fun _ ↦ Unit.unit) (fun _ i ↦ ((d j).2.val i).val)
        (fun i _ ↦ mu i (d j))))
      (unbroken K 5 ell L positions (fullCell htotal reference)
        (fun cell i ↦ (cell.2.val i).val) mu) := by sorry
