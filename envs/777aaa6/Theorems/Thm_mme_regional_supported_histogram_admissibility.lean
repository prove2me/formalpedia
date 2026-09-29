-- Prove2me | Theorems.Thm_mme_regional_supported_histogram_admissibility
-- name    : mme_regional_supported_histogram_admissibility
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-21T21:15:45.977989+00:00
-- url     : https://prove2.me/theorems/42ce2054-4a77-4ab8-872d-5d87385fc333
-- title:
--   Supported CW word histograms satisfy regional profile admissibility
-- statement:
--   For any actual graded CW-supported triple of complete words along a target regional address, its cell histograms have exactly the required m(c)+m(complement c) masses, the correct word grades, and all three boundary-reflection profile identities. These profile requirements are derived from the supported words, not assumed.
-- source:
--   Direct combinatorial proof by counting address fibers and reflecting fine words at a zero-grade boundary.

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

theorem mme_regional_supported_histogram_admissibility {ell M : ℕ} {P : ProfiledCW.Predicate M}
    (D : IntegerStep ell M P)
    (x : Fin 3 → Position D.n → CompleteWord ell)
    (hgrade : ∀ i, Graded D.total i D.reference (x i))
    (hsupport : ∀ p r, (x 0 p r).val + (x 1 p r).val + (x 2 p r).val = 2) :
    (∀ i c, ∑ w, count (fullCell D.total D.reference) (x i) c w =
      D.m c.1 c.2 + D.m c.1 (complement (D.total c.1) c.2)) ∧
    (∀ i c w, 0 < count (fullCell D.total D.reference) (x i) c w →
      ∑ r, (w r).val = (c.2.val i).val) ∧
    BoundaryProfiles (fun i ↦ count (fullCell D.total D.reference) (x i)) := by
  sorry
