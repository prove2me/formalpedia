-- Prove2me | solution 1 for mme_recursive_yz_reference_child_product_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T01:41:09.985985+00:00
-- url     : https://prove2.me/submissions/10653897-ee61-46b4-b2f3-0f369f294d2c

import Theorems.Thm_mme_recursive_yz_actual_cell_product_restriction
import Definitions.Def_mme_recursive_x_hash_families
import Definitions.Def_mme_recursive_yz_physical_words

open BigOperators MME MME.RecursiveYZ MME.RecursiveYZ.CWCells
open MME.CompleteSplit MME.TensorObj
set_option autoImplicit false
universe u

private theorem full_cell_fiber {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (a : Address half R parent n) (r : Fin R)
    (c : MME.RecursiveThinSplit.Split half (parent r)) :
    Fintype.card {p : Position n // fullCell htotal a p = ⟨r,c⟩} =
      MME.RecursiveThinSplit.count (a r) c +
      MME.RecursiveThinSplit.count (a r) (complement (htotal r) c) := by
  classical
  let e : {p : Position n // fullCell htotal a p = ⟨r,c⟩} ≃
      {p : Fin (n r) × Fin 2 //
        (if p.2 = 0 then a r p.1 else complement (htotal r) (a r p.1)) = c} := {
    toFun := by
      rintro ⟨⟨r',t,h⟩,hp⟩
      have hr : r' = r := congrArg Sigma.fst hp
      subst r'
      exact ⟨(t,h), eq_of_heq (Sigma.mk.inj hp).2⟩
    invFun := fun p ↦ ⟨⟨r,p.val⟩, by
      change (⟨r,_⟩ : Cell half R parent) = ⟨r,c⟩
      rw [p.property]⟩
    left_inv := by
      rintro ⟨⟨r',t,h⟩,hp⟩
      have hr : r' = r := congrArg Sigma.fst hp
      subst r'
      rfl
    right_inv := by intro p; rfl }
  rw [Fintype.card_congr e, Fintype.card_subtype]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  have hc (t : Fin (n r)) : complement (htotal r) (a r t) = c ↔
      a r t = complement (htotal r) c := by
    constructor
    · intro h
      simpa only [complement_complement] using congrArg (complement (htotal r)) h
    · intro h
      rw [h, complement_complement]
  simp only [show (1 : Fin 2) ≠ 0 by decide, 
    MME.RecursiveThinSplit.count, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.sum_add_distrib]
  simp only [ite_true, ite_false, hc]
  congr 1

/-- Exact address counts identify the sizes of the physical child fibers.
Their tensor product restricts from the intact reference tensor. -/
theorem solution
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
        (fun cell i ↦ (cell.2.val i).val) mu) := by
  classical
  have hcounts : ∀ r c, RecursiveThinSplit.count (reference r) c = m r c :=
    (Finset.mem_filter.mp href).2
  let D : Partition (fullCell htotal reference) := {
    parts := parts
    cells := d
    size := fun j ↦ m (d j).1 (d j).2 +
      m (d j).1 (complement (htotal (d j).1) (d j).2)
    fiber := fun j ↦ (Fintype.equivFinOfCardEq (by
      rw [full_cell_fiber htotal reference (d j).1 (d j).2, hcounts, hcounts])).symm }
  exact mme_recursive_yz_actual_cell_product_restriction
    5 ell L positions (fullCell htotal reference) (fun cell i ↦ (cell.2.val i).val) mu D


#print axioms solution
