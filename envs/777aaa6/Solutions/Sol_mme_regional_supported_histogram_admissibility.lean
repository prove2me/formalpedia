-- Prove2me | solution 1 for mme_regional_supported_histogram_admissibility
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-21T21:17:38.055861+00:00
-- url     : https://prove2.me/submissions/50983a64-7873-4293-b499-5e40f94a5eef

import Definitions.Def_mme_integer_regional_CW_recipe
import Mathlib
open BigOperators MME MME.RecursiveYZ MME.RegionRealization MME.CompleteSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000

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

private theorem histogram_mass {P C W : Type*} [Fintype P] [Fintype W]
    (cell : P → C) (f : P → W) (c : C) :
    ∑ w, count cell f c w = Fintype.card {p : P // cell p = c} := by
  classical
  simp only [count, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  rw [Fintype.card_subtype]
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : cell p = c <;> simp [hp]

private theorem histogram_reflection {P C : Type*} [Fintype P] {ell : ℕ}
    (cell : P → C) (f g : P → CompleteWord ell) (c : C)
    (h : ∀ p, cell p = c → f p = fun r ↦ Fin.rev (g p r))
    (w : CompleteWord ell) : count cell f c w = count cell g c (fun r ↦ Fin.rev (w r)) := by
  classical
  unfold count
  congr 1
  ext p
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨hp,hw⟩
    refine ⟨hp,?_⟩
    funext r
    have hh := congrFun ((h p hp).symm.trans hw) r
    simpa using congrArg Fin.rev hh
  · rintro ⟨hp,hw⟩
    refine ⟨hp,?_⟩
    rw [h p hp,hw]
    simp

theorem solution {ell M : ℕ} {P : ProfiledCW.Predicate M}
    (D : IntegerStep ell M P)
    (x : Fin 3 → Position D.n → CompleteWord ell)
    (hgrade : ∀ i, Graded D.total i D.reference (x i))
    (hsupport : ∀ p r, (x 0 p r).val + (x 1 p r).val + (x 2 p r).val = 2) :
    (∀ i c, ∑ w, count (fullCell D.total D.reference) (x i) c w =
      D.m c.1 c.2 + D.m c.1 (complement (D.total c.1) c.2)) ∧
    (∀ i c w, 0 < count (fullCell D.total D.reference) (x i) c w →
      ∑ r, (w r).val = (c.2.val i).val) ∧
    BoundaryProfiles (fun i ↦ count (fullCell D.total D.reference) (x i)) := by
  classical
  have hjoint : ∀ r c, RecursiveThinSplit.count (D.reference r) c = D.m r c :=
    (Finset.mem_filter.mp D.reference_target).2
  have hzero (i : Fin 3) (c : Cell D.half D.R D.parent)
      (hc : (c.2.val i).val = 0) (p : Position D.n)
      (hp : fullCell D.total D.reference p = c) (r : Fin (2^(ell-1))) :
      (x i p r).val = 0 := by
    have hh := hgrade i p
    rw [hp,hc] at hh
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ Nat.zero_le _)).mp hh r (Finset.mem_univ r)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i c
    rcases c with ⟨r,c⟩
    rw [histogram_mass]
    have hf := full_cell_fiber D.total D.reference r c
    rw [hjoint,hjoint] at hf
    simpa only [Fintype.card_eq_nat_card] using hf
  · intro i c w hw
    have hw' : ∃ p, fullCell D.total D.reference p = c ∧ x i p = w := by
      simpa only [count,Finset.card_pos,Finset.Nonempty,Finset.mem_filter,Finset.mem_univ,
        true_and] using hw
    obtain ⟨p,hp,hw⟩ := hw' 
    have hg := hgrade i p
    rw [hp,hw] at hg
    exact hg
  · intro c hc w
    apply histogram_reflection
    intro p hp
    funext r
    apply Fin.ext
    have hz := hzero 2 c hc p hp r
    have hs := hsupport p r
    simp only [Fin.rev,Fin.val_mk]
    omega
  · intro c hc w
    apply histogram_reflection
    intro p hp
    funext r
    apply Fin.ext
    have hz := hzero 0 c hc p hp r
    have hs := hsupport p r
    simp only [Fin.rev,Fin.val_mk]
    omega
  · intro c hc w
    apply histogram_reflection
    intro p hp
    funext r
    apply Fin.ext
    have hz := hzero 1 c hc p hp r
    have hs := hsupport p r
    simp only [Fin.rev,Fin.val_mk]
    omega
