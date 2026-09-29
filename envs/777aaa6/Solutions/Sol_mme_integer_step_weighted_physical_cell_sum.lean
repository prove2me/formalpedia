-- Prove2me | solution 1 for mme_integer_step_weighted_physical_cell_sum
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T12:32:16.692312+00:00
-- url     : https://prove2.me/submissions/f00c037e-354b-4ba1-b529-6a13dd5cb9bd

import Definitions.Def_mme_integer_regional_CW_recipe

open BigOperators MME MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.CWCells MME.RecursiveYZ.Boundary MME.ProfiledCW
set_option autoImplicit false
open MME.RegionRealization

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

/-- The size of each physical cell is its prescribed count plus the complementary count. -/
theorem mme_integer_step_physical_cell_size
    {ell M : ℕ} {P : Predicate M} (D : IntegerStep ell M P)
    (part : Partition (fullCell D.total D.reference)) (j : Fin part.parts) :
    part.size j = D.m (part.cells j).1 (part.cells j).2 +
      D.m (part.cells j).1 (complement (D.total (part.cells j).1) (part.cells j).2) := by
  classical
  have htarget : ∀ r c, RecursiveThinSplit.count (D.reference r) c = D.m r c := by
    simpa only [RecursiveXHash.target, Finset.mem_filter, Finset.mem_univ, true_and,
      RecursiveThinSplit.HasJointCounts] using D.reference_target
  have hf := full_cell_fiber D.total D.reference (part.cells j).1 (part.cells j).2
  rw [htarget, htarget] at hf
  rw [← hf, ← Fintype.card_congr (part.fiber j), Fintype.card_fin]

/-- Weighted physical cell sizes can be computed from the prescribed integer counts. -/
theorem solution
    {ell M : ℕ} {P : Predicate M} (D : IntegerStep ell M P)
    (part : Partition (fullCell D.total D.reference))
    (f : Cell D.half D.R D.parent → ℕ) :
    (∑ j, part.size j * f (part.cells j)) =
      ∑ r, ∑ c, (D.m r c + D.m r (complement (D.total r) c)) * f ⟨r, c⟩ := by
  classical
  simp_rw [mme_integer_step_physical_cell_size D part]
  calc
    _ = ∑ c : Cell D.half D.R D.parent,
        (D.m c.1 c.2 + D.m c.1 (complement (D.total c.1) c.2)) * f c :=
      Equiv.sum_comp part.cells _
    _ = _ := Fintype.sum_sigma _

#print axioms mme_integer_step_physical_cell_size
#print axioms solution
