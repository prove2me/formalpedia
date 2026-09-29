-- Prove2me | solution 1 for mme_recursive_yz_reference_partitioned_child_product_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T06:09:35.755416+00:00
-- url     : https://prove2.me/submissions/41a093ac-3bf2-47b1-97a3-a9be7388adeb

import Theorems.Thm_mme_recursive_yz_reference_child_product_restrict
import Theorems.Thm_mme_kronFin_partition_isomorphic

open BigOperators MME MME.RecursiveYZ MME.RecursiveYZ.CWCells
open MME.CompleteSplit MME.TensorObj
universe u

/-- A partition of the child cells gives a product of two child families
restricting from the same intact reference tensor, with exact physical sizes. -/
theorem solution
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
        (fun cell i ↦ (cell.2.val i).val) mu) := by
  let d : Fin (a + b) ≃ Cell half R parent := finSumFinEquiv.symm.trans e
  let child := fun c : Cell half R parent ↦ unbroken K 5 ell
    (m c.1 c.2 + m c.1 (complement (htotal c.1) c.2))
    (Equiv.refl _) (fun _ ↦ Unit.unit) (fun _ i ↦ (c.2.val i).val)
    (fun i _ ↦ mu i c)
  let T := fun j : Fin (a + b) ↦ child (d j)
  change Restrict (kron (kronFin a (fun j => child (e (.inl j))))
    (kronFin b (fun j => child (e (.inr j))))) _
  have hrefine := mme_recursive_yz_reference_child_product_restrict (K := K)
    htotal m reference href ell L (a + b) positions d mu
  have hsplit := (mme_kronFin_partition_isomorphic finSumFinEquiv T).2
  simpa only [T, d, Equiv.trans_apply, Equiv.symm_apply_apply] using hsplit.trans hrefine


#print axioms solution
