-- Prove2me | solution 1 for mme_recursive_yz_stage_block_nonempty_iff_grade_support
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T09:52:23.986251+00:00
-- url     : https://prove2.me/submissions/57edc9ae-66b6-4ead-ac7d-15ddc6e0378f

import Definitions.Def_mme_recursive_yz_stage_certificate
import Mathlib.Data.Fintype.EquivFin
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.BigOperators

open BigOperators MME MME.RecursiveYZ MME.RecursiveYZ.Certificate MME.CompleteSplit

/-- Realize a cell histogram by assigning its labeled occurrences to the cell positions. -/
theorem cellWord_nonempty_of_mass_and_grade
    {P C W G : Type*} [Fintype P] [Fintype W]
    (cell : P → C) (grade : W → G) (shape : C → G) (mu : C → W → ℕ)
    (hmass : ∀ c, ∑ w, mu c w = Nat.card {p : P // cell p = c})
    (hgrade : ∀ c w, 0 < mu c w → grade w = shape c) :
    Nonempty (CellWord cell grade shape mu) := by
  classical
  let e (c : C) : {p : P // cell p = c} ≃ Σ w : W, Fin (mu c w) :=
    Fintype.equivOfCardEq (by simpa using (hmass c).symm)
  let f (p : P) : W := (e (cell p) ⟨p, rfl⟩).1
  have he (p : P) (c : C) (hp : cell p = c) : (e c ⟨p, hp⟩).1 = f p := by
    subst c
    rfl
  refine ⟨⟨f, ?_, ?_⟩⟩
  · intro p
    exact hgrade (cell p) (f p) (Nat.zero_lt_of_lt (e (cell p) ⟨p, rfl⟩).2.isLt)
  · intro c w
    change (Finset.univ.filter (fun p => cell p = c ∧ f p = w)).card = mu c w
    have H : (Finset.univ : Finset (Fin (mu c w))).card =
        (Finset.univ.filter (fun p => cell p = c ∧ f p = w)).card := by
      apply Finset.card_bij (fun k _ => ((e c).symm ⟨w, k⟩).val)
      · intro k hk
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ((e c).symm ⟨w, k⟩).property, ?_⟩
        rw [← he _ c ((e c).symm ⟨w, k⟩).property]
        simp
      · intro k hk l hl hkl
        have hsub : (e c).symm ⟨w, k⟩ = (e c).symm ⟨w, l⟩ := Subtype.ext hkl
        have hs := (e c).symm.injective hsub
        cases hs
        rfl
      · intro p hp
        obtain ⟨_, hpc, hpw⟩ := Finset.mem_filter.mp hp
        have hw : (e c ⟨p, hpc⟩).1 = w := (he p c hpc).trans hpw
        let k : Fin (mu c w) := hw ▸ (e c ⟨p, hpc⟩).2
        refine ⟨k, Finset.mem_univ _, ?_⟩
        have hs : (⟨w, k⟩ : Σ v : W, Fin (mu c v)) = e c ⟨p, hpc⟩ := by
          dsimp [k]
          cases hw
          rfl
        rw [hs, Equiv.symm_apply_apply]
    simpa using H.symm

/-- Cellwise mass and grade support exactly characterize profile-block feasibility. -/
theorem cellWord_nonempty_iff_mass_and_grade
    {P C W G : Type*} [Fintype P] [Fintype W]
    (cell : P → C) (grade : W → G) (shape : C → G) (mu : C → W → ℕ) :
    Nonempty (CellWord cell grade shape mu) ↔
      (∀ c, ∑ w, mu c w = Nat.card {p : P // cell p = c}) ∧
      (∀ c w, 0 < mu c w → grade w = shape c) := by
  classical
  constructor
  · rintro ⟨f⟩
    constructor
    · intro c
      have h := Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ.filter (fun p => cell p = c)) Finset.univ f.val
      simp only [Finset.mem_univ, Finset.filter_filter] at h
      have hmass : (∑ w, count cell f.val c w) = Nat.card {p : P // cell p = c} := by
        simpa [count, Nat.card_eq_fintype_card, Fintype.card_subtype] using h
      have hf (w : W) : count cell f.val c w = mu c w := f.property.2 c w
      simpa only [hf] using hmass
    · intro c w hw
      have hcount : 0 < count cell f.val c w := by
        rw [f.property.2 c w]
        exact hw
      obtain ⟨p, hp⟩ := Finset.card_pos.mp hcount
      have hp' : cell p = c ∧ f.val p = w := (Finset.mem_filter.mp hp).2
      simpa only [hp'.1, hp'.2] using f.property.1 p
  · rintro ⟨hmass, hgrade⟩
    exact cellWord_nonempty_of_mass_and_grade cell grade shape mu hmass hgrade

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

/-- The stored stage mass identities leave grade support as the exact block-feasibility test. -/
theorem stage_block_nonempty_iff_grade_support
    {D : HashExtraction.HashData} (A : Stage D) (i : Fin 3) :
    Nonempty (CWCells.Block A.ell (fullCell A.total A.reference)
      (fun c i => (c.2.val i).val) A.mu i) ↔
    ∀ c w, 0 < A.mu i c w → CWCells.grade w = (c.2.val i).val := by
  classical
  have htarget := (Finset.mem_filter.mp A.reference_target).2
  have hmass (c : Cell D.half D.R D.parent) :
      ∑ w, A.mu i c w = Nat.card {p : Position D.n // fullCell A.total A.reference p = c} := by
    obtain ⟨r, c⟩ := c
    rw [A.mass, Nat.card_eq_fintype_card, full_cell_fiber,
      htarget r c, htarget r (complement (A.total r) c)]
  exact (cellWord_nonempty_iff_mass_and_grade
    (fullCell A.total A.reference) CWCells.grade
    (fun c => (c.2.val i).val) (A.mu i)).trans (and_iff_right hmass)


theorem solution
    {D : HashExtraction.HashData} (A : Stage D) (i : Fin 3) :
    Nonempty (CWCells.Block A.ell (fullCell A.total A.reference)
      (fun c i => (c.2.val i).val) A.mu i) ↔
    ∀ c w, 0 < A.mu i c w → CWCells.grade w = (c.2.val i).val := by
  exact stage_block_nonempty_iff_grade_support A i
#print axioms solution
