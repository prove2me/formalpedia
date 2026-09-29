-- Prove2me | solution 1 for mme_recursive_yz_scaled_reference_partitioned_child_product_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T06:16:44.654253+00:00
-- url     : https://prove2.me/submissions/19dfdbb8-e6b0-4048-92ea-a2094dbb4240

import Theorems.Thm_mme_recursive_yz_reference_partitioned_child_product_restrict

open BigOperators MME MME.RecursiveYZ MME.RecursiveYZ.CWCells
open MME.CompleteSplit MME.TensorObj
universe u

/-- A common replication factor can be pulled outside each child size in
the partitioned reference restriction, including zero replication and empty cells. -/
theorem solution
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
        (fun cell i ↦ (cell.2.val i).val) mu) := by
  let raw := fun c : Cell half R parent ↦ unbroken K 5 ell
    (k * m c.1 c.2 + k * m c.1 (complement (htotal c.1) c.2))
    (Equiv.refl _) (fun _ ↦ Unit.unit) (fun _ i ↦ (c.2.val i).val)
    (fun i _ ↦ mu i c)
  let child := fun c : Cell half R parent ↦ unbroken K 5 ell
    (k * (m c.1 c.2 + m c.1 (complement (htotal c.1) c.2)))
    (Equiv.refl _) (fun _ ↦ Unit.unit) (fun _ i ↦ (c.2.val i).val)
    (fun i _ ↦ mu i c)
  have hchild (c : Cell half R parent) : raw c = child c := by
    exact congrArg (fun N => unbroken K 5 ell N (Equiv.refl _)
      (fun _ ↦ Unit.unit) (fun _ i ↦ (c.2.val i).val) (fun i _ ↦ mu i c))
      (Nat.mul_add k (m c.1 c.2) (m c.1 (complement (htotal c.1) c.2))).symm
  have h := mme_recursive_yz_reference_partitioned_child_product_restrict (K := K)
    htotal (fun r c => k * m r c) reference href ell L a b positions e mu
  change Restrict (kron (kronFin a (fun j => raw (e (.inl j))))
    (kronFin b (fun j => raw (e (.inr j))))) _ at h
  change Restrict (kron (kronFin a (fun j => child (e (.inl j))))
    (kronFin b (fun j => child (e (.inr j))))) _
  simpa only [hchild] using h


#print axioms solution
