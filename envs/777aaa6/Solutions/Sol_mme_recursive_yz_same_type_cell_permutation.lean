-- Prove2me | solution 1 for mme_recursive_yz_same_type_cell_permutation
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-12T11:07:33.475083+00:00
-- url     : https://prove2.me/submissions/3d516e5b-4061-49b6-82e8-542c499cc9e4

import Definitions.Def_mme_recursive_yz_physical_words
import Definitions.Def_mme_recursive_x_hash_families
open BigOperators MME MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 800000

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

theorem solution {half R : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (a b : Address half R parent n)
    (ha : a ∈ RecursiveXHash.target m) (hb : b ∈ RecursiveXHash.target m) :
    ∃ sigma : Equiv.Perm (Position n), ∀ p, fullCell htotal a (sigma p) = fullCell htotal b p := by
  classical
  have hat : ∀ r c, RecursiveThinSplit.count (a r) c = m r c := by
    simpa only [RecursiveXHash.target,RecursiveThinSplit.HasJointCounts,Finset.mem_filter,Finset.mem_univ,true_and] using ha
  have hbt : ∀ r c, RecursiveThinSplit.count (b r) c = m r c := by
    simpa only [RecursiveXHash.target,RecursiveThinSplit.HasJointCounts,Finset.mem_filter,Finset.mem_univ,true_and] using hb
  have hcard (c : Cell half R parent) :
      Fintype.card {p : Position n // fullCell htotal b p = c} =
        Fintype.card {p : Position n // fullCell htotal a p = c} := by
    obtain ⟨r,c⟩ := c
    rw [full_cell_fiber,full_cell_fiber,hat r c,hbt r c,
      hat r (complement (htotal r) c),hbt r (complement (htotal r) c)]
  let es := fun c ↦ Fintype.equivOfCardEq (hcard c)
  exact ⟨Equiv.ofFiberEquiv es,Equiv.ofFiberEquiv_map es⟩
