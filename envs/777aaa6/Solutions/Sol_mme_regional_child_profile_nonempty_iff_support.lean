-- Prove2me | solution 1 for mme_regional_child_profile_nonempty_iff_support
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T13:31:45.621882+00:00
-- url     : https://prove2.me/submissions/0d6edfe9-eda8-48b9-9653-e73e202cd8dc

import Theorems.Thm_mme_recursive_cellWord_nonempty_iff_mass_and_grade

open BigOperators MME MME.RecursiveYZ MME.CompleteSplit
open scoped Classical
set_option autoImplicit false

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

/-- Exact split counts and complementary child masses reduce physical
profile feasibility to the grade-support condition. -/
theorem solution
    {half R : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    {W G : Type*} [Fintype W]
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (a : Address half R parent n) (ha : a ∈ RecursiveXHash.target m)
    (grade : W → G) (shape : Cell half R parent → G)
    (mu : Cell half R parent → W → ℕ)
    (hmass : ∀ c, ∑ w, mu c w = m c.1 c.2 +
      m c.1 (complement (htotal c.1) c.2)) :
    Nonempty (CellWord (fullCell htotal a) grade shape mu) ↔
      ∀ c w, 0 < mu c w → grade w = shape c := by
  classical
  have htarget : ∀ r c, RecursiveThinSplit.count (a r) c = m r c := by
    simpa only [RecursiveXHash.target, Finset.mem_filter, Finset.mem_univ,
      true_and, RecursiveThinSplit.HasJointCounts] using ha
  have hphysical (c : Cell half R parent) :
      ∑ w, mu c w = Nat.card {p : Position n // fullCell htotal a p = c} := by
    obtain ⟨r,c⟩ := c
    rw [hmass, Nat.card_eq_fintype_card, full_cell_fiber, htarget, htarget]
  exact (mme_recursive_cellWord_nonempty_iff_mass_and_grade
    (fullCell htotal a) grade shape mu).trans (and_iff_right hphysical)

#print axioms solution
