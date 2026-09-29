-- Prove2me | solution 1 for mme_finset_weighted_collision_averaging_isolated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T18:58:10.455743+00:00
-- url     : https://prove2.me/submissions/c03190fc-a649-496f-9fb4-c59143e50951

import Mathlib
import Theorems.Thm_mme_finite_collision_budget_averaging_real

open BigOperators

set_option autoImplicit false
set_option warningAsError true

private theorem weighted_target_isolation_pruning
    {Edge X Y : Type}
    [DecidableEq Edge] [DecidableEq X] [DecidableEq Y]
    (target ambient : Finset Edge) (htarget : target ⊆ ambient)
    (x : Edge → X) (y : Edge → Y)
    (mass : Edge → ℕ) (cap : ℕ)
    (hmass : ∀ a ∈ target, mass a ≤ cap) :
    let collisions := (target.product ambient).filter (fun q ↦
      q.1 ≠ q.2 ∧ (x q.1 = x q.2 ∨ y q.1 = y q.2))
    ∃ isolated : Finset Edge,
      isolated ⊆ target ∧
      isolated ⊆ ambient ∧
      (∀ e ∈ isolated, ∀ e' ∈ ambient,
        x e = x e' ∨ y e = y e' → e = e') ∧
      (∑ a ∈ target, mass a) ≤
        (∑ a ∈ isolated, mass a) + cap * collisions.card := by
  classical
  dsimp only
  let Isolated : Edge → Prop := fun e ↦
    ∀ e' ∈ ambient, x e = x e' ∨ y e = y e' → e = e'
  let isolated := target.filter Isolated
  let collisions := (target.product ambient).filter (fun q ↦
    q.1 ≠ q.2 ∧ (x q.1 = x q.2 ∨ y q.1 = y q.2))
  have hisolatedTarget : isolated ⊆ target := Finset.filter_subset _ _
  have hnot (e : Edge) (he : e ∈ target \ isolated) : ¬ Isolated e := by
    have he' := Finset.mem_sdiff.mp he
    intro hiso
    exact he'.2 (Finset.mem_filter.mpr ⟨he'.1, hiso⟩)
  have hcompetitor (e : Edge) (he : e ∈ target \ isolated) :
      ∃ e' ∈ ambient, e ≠ e' ∧ (x e = x e' ∨ y e = y e') := by
    have hn := hnot e he
    simp only [Isolated] at hn
    push_neg at hn
    obtain ⟨e', he'Ambient, hshare, hne⟩ := hn
    exact ⟨e', he'Ambient, hne, hshare⟩
  let competitor : Edge → Edge := fun e ↦
    if he : e ∈ target \ isolated then Classical.choose (hcompetitor e he)
    else e
  have hcompetitor_spec (e : Edge) (he : e ∈ target \ isolated) :
      competitor e ∈ ambient ∧ e ≠ competitor e ∧
        (x e = x (competitor e) ∨ y e = y (competitor e)) := by
    simp only [competitor, dif_pos he]
    exact ⟨(Classical.choose_spec (hcompetitor e he)).1,
      (Classical.choose_spec (hcompetitor e he)).2.1,
      (Classical.choose_spec (hcompetitor e he)).2.2⟩
  let f : Edge → Edge × Edge := fun e ↦ (e, competitor e)
  have hmaps : Set.MapsTo f (↑(target \ isolated) : Set Edge)
      (↑collisions : Set (Edge × Edge)) := by
    intro e he
    have heFin : e ∈ target \ isolated := he
    have he' := Finset.mem_sdiff.mp heFin
    have hs := hcompetitor_spec e heFin
    exact Finset.mem_filter.mpr ⟨
      Finset.mem_product.mpr ⟨he'.1, hs.1⟩, hs.2.1, hs.2.2⟩
  have hinj : Set.InjOn f (↑(target \ isolated) : Set Edge) := by
    intro a ha b hb hab
    exact congrArg Prod.fst hab
  have hdeleted : (target \ isolated).card ≤ collisions.card :=
    Finset.card_le_card_of_injOn f hmaps hinj
  have hdeletedMass :
      (∑ a ∈ target \ isolated, mass a) ≤ cap * collisions.card := by
    calc
      (∑ a ∈ target \ isolated, mass a) ≤
          (target \ isolated).card * cap := by
        simpa [mul_comm] using
          (target \ isolated).sum_le_card_nsmul mass cap (fun a ha ↦
            hmass a (Finset.mem_sdiff.mp ha).1)
      _ ≤ collisions.card * cap := Nat.mul_le_mul_right cap hdeleted
      _ = cap * collisions.card := Nat.mul_comm _ _
  refine ⟨isolated, hisolatedTarget,
    fun a ha ↦ htarget (hisolatedTarget ha), ?_, ?_⟩
  · intro e he e' he' hshare
    exact (Finset.mem_filter.mp he).2 e' he' hshare
  · have hpartition :
        (∑ a ∈ target, mass a) =
          (∑ a ∈ isolated, mass a) +
            ∑ a ∈ target \ isolated, mass a := by
      rw [← Finset.sum_union]
      · congr 1
        exact (Finset.union_sdiff_of_subset hisolatedTarget).symm
      · exact Finset.disjoint_sdiff
    rw [hpartition]
    exact Nat.add_le_add_left hdeletedMass _

theorem solution
    {State Edge X Y : Type}
    [Fintype State] [Nonempty State] [DecidableEq State]
    [DecidableEq Edge] [DecidableEq X] [DecidableEq Y]
    (target : Finset Edge) (ambient : State → Finset Edge)
    (x : Edge → X) (y : Edge → Y)
    (mass : State → Edge → ℕ) (cap : ℕ) (lower : ℝ)
    (hmass : ∀ q a, a ∈ target → a ∈ ambient q → mass q a ≤ cap)
    (hbudget :
      (Fintype.card State : ℝ) * lower +
          ∑ q, ((cap *
            (((target.filter (fun a ↦ a ∈ ambient q)).product
              (ambient q)).filter (fun pair ↦
                pair.1 ≠ pair.2 ∧
                  (x pair.1 = x pair.2 ∨ y pair.1 = y pair.2))).card : ℕ) : ℝ) ≤
        ∑ q, (((∑ a ∈ target.filter (fun a ↦ a ∈ ambient q),
          mass q a) : ℕ) : ℝ)) :
    ∃ q : State, ∃ isolated : Finset Edge,
      isolated ⊆ target ∧
      isolated ⊆ ambient q ∧
      (∀ e ∈ isolated, ∀ e' ∈ ambient q,
        x e = x e' ∨ y e = y e' → e = e') ∧
      lower ≤ ((∑ a ∈ isolated, mass q a : ℕ) : ℝ) := by
  classical
  let localTarget : State → Finset Edge := fun q ↦
    target.filter (fun a ↦ a ∈ ambient q)
  let collisions : State → Finset (Edge × Edge) := fun q ↦
    ((localTarget q).product (ambient q)).filter (fun pair ↦
      pair.1 ≠ pair.2 ∧
        (x pair.1 = x pair.2 ∨ y pair.1 = y pair.2))
  let retainedMass : State → ℕ := fun q ↦
    ∑ a ∈ localTarget q, mass q a
  let collisionCost : State → ℕ := fun q ↦ cap * (collisions q).card
  have hbudget' :
      (Fintype.card State : ℝ) * lower +
          ∑ q, (collisionCost q : ℝ) ≤
        ∑ q, (retainedMass q : ℝ) := by
    simpa only [localTarget, collisions, retainedMass, collisionCost] using hbudget
  obtain ⟨q, hq⟩ := mme_finite_collision_budget_averaging_real
    retainedMass collisionCost lower hbudget'
  have hlocalAmbient : localTarget q ⊆ ambient q := by
    intro a ha
    exact (Finset.mem_filter.mp ha).2
  obtain ⟨isolated, hIlocal, hIambient, hIsolated, hMass⟩ :=
    weighted_target_isolation_pruning
      (localTarget q) (ambient q) hlocalAmbient x y (mass q) cap
      (fun a ha ↦ hmass q a (Finset.mem_filter.mp ha).1
        (Finset.mem_filter.mp ha).2)
  refine ⟨q, isolated, ?_, hIambient, hIsolated, ?_⟩
  · intro a ha
    exact (Finset.mem_filter.mp (hIlocal ha)).1
  · have hMassR :
        (retainedMass q : ℝ) ≤
          ((∑ a ∈ isolated, mass q a : ℕ) : ℝ) +
            (collisionCost q : ℝ) := by
      exact_mod_cast hMass
    norm_num only [add_comm] at hq
    linarith
