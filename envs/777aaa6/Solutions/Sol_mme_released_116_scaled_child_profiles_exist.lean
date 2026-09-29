-- Prove2me | solution 1 for mme_released_116_scaled_child_profiles_exist
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T13:35:51.430213+00:00
-- url     : https://prove2.me/submissions/24f3edb6-90b6-472b-a3d0-e17f1001252b

import Theorems.Thm_mme_released_116_integer_profile_support
import Theorems.Thm_mme_released_116_integer_profile_mass
import Theorems.Thm_mme_released_116_regional_split_mass
import Theorems.Thm_mme_recursive_cellWord_nonempty_iff_mass_and_grade
import Theorems.Thm_mme_released_116_weighted_parent_center
import Definitions.Def_mme_recursive_x_hash_families
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sigma

open BigOperators MME MME.RecursiveThinSplit MME.RecursiveXHash
open scoped Classical
set_option autoImplicit false

/-- Exact split histograms are realizable precisely when each regional mass
matches its number of physical positions. -/
theorem mme_regional_reference_exists_iff_mass
    {half R : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (m : ∀ r, Split half (parent r) → ℕ) :
    (∃ a : RecursiveXHash.Address half R parent n, a ∈ target m) ↔
      ∀ r, ∑ c, m r c = n r := by
  classical
  constructor
  · rintro ⟨a, ha⟩ r
    have hc := (Finset.mem_filter.mp ha).2 r
    change ∀ c, count (a r) c = m r c at hc
    have hsum := Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Fin (n r))) Finset.univ (a r)
    simp only [Finset.mem_univ, Finset.filter_true, Finset.card_univ,
      Fintype.card_fin] at hsum
    change (∑ c, count (a r) c) = n r at hsum
    simpa only [hc] using hsum
  · intro hmass
    let e (r : Fin R) : Fin (n r) ≃ Σ c, Fin (m r c) :=
      Fintype.equivOfCardEq (by
        rw [Fintype.card_fin, Fintype.card_sigma]
        simpa only [Fintype.card_fin] using (hmass r).symm)
    let a : RecursiveXHash.Address half R parent n := fun r t => (e r t).1
    refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro r c
    rw [count, ← Fintype.card_subtype]
    let ef : {t : Fin (n r) // a r t = c} ≃
        {p : (Σ c, Fin (m r c)) // p.1 = c} :=
      Equiv.subtypeEquiv (e r) (fun _ => Iff.rfl)
    rw [Fintype.card_congr ef, Fintype.card_congr (Equiv.sigmaSubtype c),
      Fintype.card_fin]


open MME.Released116 MME.MoreAsymmetryExactSeed

/-- All integer multiples of the released regional split histograms admit
physical reference assignments, including the empty scaling. -/
theorem mme_released_116_scaled_reference_exists (k : ℕ) :
    ∃ a : RecursiveXHash.Address 4 6 parent (fun r => k * regionalSize r),
      a ∈ target (fun r c => k * splitCount r c) := by
  apply (mme_regional_reference_exists_iff_mass _).mpr
  intro r
  rw [← Finset.mul_sum]
  simpa only [parent] using
    congrArg (fun x : ℕ => k * x) (mme_released_116_regional_split_mass r).2


open MME.RecursiveYZ MME.CompleteSplit

private theorem full_cell_fiber {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (a : RecursiveXHash.Address half R parent n) (r : Fin R)
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
theorem mme_regional_child_profile_nonempty_iff_support
    {half R : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    {W G : Type*} [Fintype W]
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (a : RecursiveXHash.Address half R parent n) (ha : a ∈ RecursiveXHash.target m)
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


/-- At every integer scale one common reference assignment supports the
prescribed child profile in each of the three modes. -/
theorem solution (k : ℕ) :
    ∃ a : RecursiveXHash.Address 4 6 parent (fun r => k * regionalSize r),
      a ∈ RecursiveXHash.target (fun r c => k * splitCount r c) ∧
      ∀ i : Fin 3, Nonempty (CellWord (fullCell parent_total a)
        (fun w : CompleteWord 2 => ∑ h, (w h).val)
        (fun c => (c.2.val i).val)
        (fun c w => k * integerProfile i c w)) := by
  classical
  obtain ⟨a,ha⟩ := mme_released_116_scaled_reference_exists k
  refine ⟨a, ha, ?_⟩
  intro i
  apply (mme_regional_child_profile_nonempty_iff_support parent_total
    (fun r c => k * splitCount r c) a ha
    (fun w : CompleteWord 2 => ∑ h, (w h).val)
    (fun c => (c.2.val i).val) (fun c w => k * integerProfile i c w) ?_).mpr
  · intro c w hw
    exact mme_released_116_integer_profile_support i c w
      (Nat.pos_of_mul_pos_left hw)
  · intro c
    rw [← Finset.mul_sum, mme_released_116_integer_profile_mass, Nat.mul_add]
    rfl

#print axioms solution
