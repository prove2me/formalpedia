-- Prove2me | solution 1 for mme_recursive_yz_exact_compatibility_card
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-12T10:18:14.541915+00:00
-- url     : https://prove2.me/submissions/f5494146-e74a-498d-8dbf-5365d1cae970

import Definitions.Def_mme_recursive_yz_physical_words
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card

open BigOperators MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false

private theorem count_coarsen {P C W G : Type*} [Fintype P] [Fintype C]
    (cell : P → C) (f : P → W) (group : C → G) (g : G) (w : W) :
    count (group ∘ cell) f g w = ∑ c, if group c = g then count cell f c w else 0 := by
  classical
  simp only [count, Finset.card_eq_sum_ones, Finset.sum_filter]
  have pull (c : C) :
      (if group c = g then ∑ p, if cell p = c ∧ f p = w then (1 : ℕ) else 0 else 0) =
      ∑ p, if group c = g then (if cell p = c ∧ f p = w then (1 : ℕ) else 0) else 0 := by
    by_cases h : group c = g <;> simp [h]
  simp_rw [pull]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : f p = w
  · simp only [h, and_true, Function.comp_apply]
    rw [Finset.sum_eq_single (cell p)]
    · simp
    · intro c hc hcp
      simp [Ne.symm hcp]
    · simp
  · simp [h]

private theorem part_left {C G : Type*} (boundary : C → Prop) (group : C → G)
    (c : C) (d : {c : C // boundary c}) :
    part boundary group c = Sum.inl d ↔ c = d.val := by
  classical
  unfold part
  split_ifs with h
  · simp only [Sum.inl.injEq, Subtype.ext_iff]
  · simp only [false_iff]
    intro heq
    exact h (heq ▸ d.property)

private theorem part_right {C G : Type*} (boundary : C → Prop) (group : C → G)
    (c : C) (g : G) :
    part boundary group c = Sum.inr g ↔ ¬ boundary c ∧ group c = g := by
  classical
  unfold part
  split_ifs with h <;> simp [h]

private theorem count_part_left {P C W G : Type*} [Fintype P]
    (cell : P → C) (f : P → W) (boundary : C → Prop) (group : C → G)
    (c : {c : C // boundary c}) (w : W) :
    count (part boundary group ∘ cell) f (Sum.inl c) w = count cell f c.val w := by
  classical
  unfold count
  simp only [Function.comp_apply, part_left]

private theorem count_part_right {P C W G : Type*} [Fintype P] [Fintype C]
    (cell : P → C) (f : P → W) (boundary : C → Prop) (group : C → G)
    (g : G) (w : W) :
    count (part boundary group ∘ cell) f (Sum.inr g) w =
      ∑ c, if ¬ boundary c ∧ group c = g then count cell f c w else 0 := by
  classical
  simpa only [part_right] using count_coarsen cell f (part boundary group) (Sum.inr g) w

private theorem partition_criterion {P C W G : Type*} [Fintype P] [Fintype C]
    (cell : P → C) (boundary : C → Prop) (group : C → G)
    (mu : C → W → ℕ) (f : P → W) :
    Compatible cell boundary group mu f ↔
      Useful (part boundary group ∘ cell) (partCount boundary group mu) f := by
  classical
  have split_sum (g : G) (v : C → ℕ) :
      (∑ c, if group c = g then v c else 0) =
      (∑ c, if boundary c ∧ group c = g then v c else 0) +
      (∑ c, if ¬ boundary c ∧ group c = g then v c else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    by_cases hb : boundary c <;> by_cases hg : group c = g <;> simp [hb,hg]
  constructor
  · rintro ⟨hb,hg⟩ s w
    cases s with
    | inl c => simpa only [count_part_left, partCount] using hb c.val c.property w
    | inr g =>
      rw [count_part_right]
      change (∑ c, if ¬ boundary c ∧ group c = g then count cell f c w else 0) = _
      have hboundary : (∑ c, if boundary c ∧ group c = g then count cell f c w else 0) =
          ∑ c, if boundary c ∧ group c = g then mu c w else 0 := by
        apply Finset.sum_congr rfl
        intro c hc
        split_ifs with h
        · rw [hb c h.1 w]
        · rfl
      have h := hg g w
      rw [count_coarsen, split_sum, split_sum, hboundary] at h
      exact Nat.add_left_cancel h
  · intro h
    constructor
    · intro c hc w
      simpa only [Useful, count_part_left, partCount] using h (Sum.inl ⟨c,hc⟩) w
    · intro g w
      rw [count_coarsen, split_sum, split_sum]
      have hboundary : (∑ c, if boundary c ∧ group c = g then count cell f c w else 0) =
          ∑ c, if boundary c ∧ group c = g then mu c w else 0 := by
        apply Finset.sum_congr rfl
        intro c hc
        split_ifs with hb
        · simpa only [count_part_left, partCount] using h (Sum.inl ⟨c,hb.1⟩) w
        · rfl
      have hinterior := h (Sum.inr g) w
      rw [count_part_right] at hinterior
      exact congrArg₂ (· + ·) hboundary hinterior

private theorem fiber_card {P C W : Type*} [Fintype P]
    (cell : P → C) (f : P → W) (c : C) (w : W) :
    Fintype.card {p : {p : P // cell p = c} // f p.val = w} = count cell f c w := by
  classical
  rw [count, ← Fintype.card_coe]
  apply Fintype.card_congr
  exact {
    toFun := fun p ↦ ⟨p.val.val, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, p.val.property, p.property⟩⟩
    invFun := fun p ↦ ⟨⟨p.val, (Finset.mem_filter.mp p.property).2.1⟩,
      (Finset.mem_filter.mp p.property).2.2⟩
    left_inv := by intro p; rfl
    right_inv := by intro p; rfl }

private theorem histogram_card {P C W : Type*} [Fintype P] [Fintype C] [Fintype W]
    (cell : P → C) (mu : C → W → ℕ)
    (hsum : ∀ c, ∑ w, mu c w = Fintype.card {p : P // cell p = c}) :
    Fintype.card {f : P → W // Useful cell mu f} =
      ∏ c, (Fintype.card {p : P // cell p = c}).factorial / ∏ w, (mu c w).factorial := by
  classical
  let Family := fun c ↦ {g : {p : P // cell p = c} → W //
    ∀ w, Fintype.card {p // g p = w} = mu c w}
  have reconstruct (F : ∀ c, Family c) (c : C) :
      (fun p : {p : P // cell p = c} ↦ (F (cell p.val)).val ⟨p.val,rfl⟩) = (F c).val := by
    funext p
    obtain ⟨p,hp⟩ := p
    subst c
    rfl
  let e : {f : P → W // Useful cell mu f} ≃ (∀ c, Family c) := {
    toFun := fun f c ↦ ⟨fun p ↦ f.val p.val, by
      intro w
      rw [fiber_card]
      exact f.property c w⟩
    invFun := fun F ↦ ⟨fun p ↦ (F (cell p)).val ⟨p,rfl⟩, by
      intro c w
      rw [← fiber_card]
      have hh := congrFun (reconstruct F c)
      simp_rw [hh]
      exact (F c).property w⟩
    left_inv := by intro f; rfl
    right_inv := by
      intro F
      funext c
      apply Subtype.ext
      exact reconstruct F c }
  rw [Fintype.card_congr e, Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro c hc
  exact mme_fintype_prescribed_fiber_function_card (mu c) (hsum c)
private theorem cell_card_coarsen {P C G : Type*} [Fintype P] [Fintype C]
    (cell : P → C) (group : C → G) (g : G) :
    Fintype.card {p : P // group (cell p) = g} =
      ∑ c, if group c = g then Fintype.card {p : P // cell p = c} else 0 := by
  classical
  simpa [count, Fintype.card_subtype] using
    count_coarsen cell (fun _ ↦ ()) group g ()

private theorem part_mass {P C W G : Type*} [Fintype P] [Fintype C] [Fintype W]
    (cell : P → C) (boundary : C → Prop) (group : C → G)
    (mu : C → W → ℕ)
    (hsum : ∀ c, ∑ w, mu c w = Fintype.card {p : P // cell p = c})
    (s : {c : C // boundary c} ⊕ G) :
    ∑ w, partCount boundary group mu s w =
      Fintype.card {p : P // part boundary group (cell p) = s} := by
  classical
  cases s with
  | inl c => simpa only [partCount, part_left] using hsum c.val
  | inr g =>
    calc
      _ = ∑ c, if part boundary group c = Sum.inr g then
          Fintype.card {p : P // cell p = c} else 0 := by
        simp only [partCount]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro c hc
        simp only [part_right]
        by_cases h : ¬ boundary c ∧ group c = g
        · simp [h, hsum]
        · simp [h]
      _ = _ := by
        convert (cell_card_coarsen cell (part boundary group) (Sum.inr g)).symm using 1 <;>
          congr 1 <;> first | exact Subsingleton.elim _ _ | (funext c; split_ifs <;> rfl)

private theorem compatible_card {P C W G : Type*}
    [Fintype P] [Fintype C] [Fintype W] [Fintype G]
    (cell : P → C) (boundary : C → Prop) (group : C → G)
    (mu : C → W → ℕ)
    (hsum : ∀ c, ∑ w, mu c w = Fintype.card {p : P // cell p = c}) :
    Fintype.card {f : P → W // Compatible cell boundary group mu f} =
      ∏ s : {c : C // boundary c} ⊕ G,
        (∑ w, partCount boundary group mu s w).factorial /
          ∏ w, (partCount boundary group mu s w).factorial := by
  classical
  let e := Equiv.subtypeEquivRight (partition_criterion cell boundary group mu)
  rw [Fintype.card_congr e]
  have hh := histogram_card (part boundary group ∘ cell) (partCount boundary group mu)
    (by intro s; convert part_mass cell boundary group mu hsum s using 1 <;> congr 1 <;> exact Subsingleton.elim _ _)
  calc
    _ = _ := hh
    _ = _ := by
      apply Finset.prod_congr rfl
      intro s hs
      congr 2
      convert (part_mass cell boundary group mu hsum s).symm using 1 <;> congr 1 <;> exact Subsingleton.elim _ _

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

private theorem compatible_nat_card {P C W G : Type*}
    [Fintype P] [Fintype C] [Fintype W] [Fintype G]
    (cell : P → C) (boundary : C → Prop) (group : C → G)
    (mu : C → W → ℕ)
    (hsum : ∀ c, ∑ w, mu c w = Nat.card {p : P // cell p = c}) :
    Nat.card {f : P → W // Compatible cell boundary group mu f} =
      compatibilityNumber boundary group mu := by
  classical
  rw [Nat.card_eq_fintype_card]
  unfold compatibilityNumber histogramNumber
  exact compatible_card cell boundary group mu
    (by intro c; simpa only [Nat.card_eq_fintype_card] using hsum c)

theorem solution {half R : ℕ} {W G : Type*} [Fintype W] [Fintype G]
    (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (a : Address half R parent n)
    (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ)
    (htype : ∀ r, MME.RecursiveThinSplit.HasJointCounts (a r) (m r))
    (boundary : Cell half R parent → Prop) (group : Cell half R parent → G)
    (mu : Cell half R parent → W → ℕ)
    (hmass : ∀ c, ∑ w, mu c w = m c.1 c.2 + m c.1 (complement (htotal c.1) c.2)) :
    Nat.card {f : Position n → W //
        Compatible (fullCell htotal a) boundary group mu f} =
      compatibilityNumber boundary group mu := by
  classical
  have hm (c : Cell half R parent) :
      Nat.card {p : Position n // fullCell htotal a p = c} =
        m c.1 c.2 + m c.1 (complement (htotal c.1) c.2) := by
    obtain ⟨r,c⟩ := c
    rw [Nat.card_eq_fintype_card, full_cell_fiber, htype r c,
      htype r (complement (htotal r) c)]
  exact compatible_nat_card (fullCell htotal a) boundary group mu
    (fun c ↦ (hmass c).trans (hm c).symm)
