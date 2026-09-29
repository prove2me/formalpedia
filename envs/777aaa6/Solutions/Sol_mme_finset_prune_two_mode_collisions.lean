-- Prove2me | solution 1 for mme_finset_prune_two_mode_collisions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T19:55:11.876464+00:00
-- url     : https://prove2.me/submissions/2d387d1d-491c-4482-9e31-5d56b9a3a201

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Prod

/-- Deleting every vertex which participates in an `x`- or `y`-collision
leaves a set injective in both labels.  Each deletion injects, by its first
coordinate, into the ordered collision-pair set. -/
theorem solution
    {α β γ : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (E : Finset α) (x : α → β) (y : α → γ) :
    ∃ F : Finset α,
      F ⊆ E ∧
      Set.InjOn x (F : Set α) ∧
      Set.InjOn y (F : Set α) ∧
      E.card ≤ F.card +
        ((E.product E).filter (fun p =>
          p.1 ≠ p.2 ∧ (x p.1 = x p.2 ∨ y p.1 = y p.2))).card := by
  classical
  let collisionPairs : Finset (α × α) :=
    (E.product E).filter (fun p =>
      p.1 ≠ p.2 ∧ (x p.1 = x p.2 ∨ y p.1 = y p.2))
  let F : Finset α := E.filter (fun e =>
    ∀ e' ∈ E, e ≠ e' → x e ≠ x e' ∧ y e ≠ y e')
  have hFE : F ⊆ E := by
    intro e he
    exact (Finset.mem_filter.mp he).1
  have hxinj : Set.InjOn x (F : Set α) := by
    intro a ha b hb hab
    have ha' : a ∈ F := ha
    have hb' : b ∈ F := hb
    by_contra hne
    have hsep := (Finset.mem_filter.mp ha').2 b (hFE hb') hne
    exact hsep.1 hab
  have hyinj : Set.InjOn y (F : Set α) := by
    intro a ha b hb hab
    have ha' : a ∈ F := ha
    have hb' : b ∈ F := hb
    by_contra hne
    have hsep := (Finset.mem_filter.mp ha').2 b (hFE hb') hne
    exact hsep.2 hab
  have hbadExists (e : ↥(E \ F)) :
      ∃ e' : α, e' ∈ E ∧ e.1 ≠ e' ∧
        (x e.1 = x e' ∨ y e.1 = y e') := by
    have heEF := Finset.mem_sdiff.mp e.2
    have henot : ¬ ∀ e' ∈ E, e.1 ≠ e' →
        x e.1 ≠ x e' ∧ y e.1 ≠ y e' := by
      intro h
      exact heEF.2 (Finset.mem_filter.mpr ⟨heEF.1, h⟩)
    push_neg at henot
    obtain ⟨e', he'E, hne, hcollision⟩ := henot
    exact ⟨e', he'E, hne, by tauto⟩
  let other (e : ↥(E \ F)) : α := Classical.choose (hbadExists e)
  have hother (e : ↥(E \ F)) :
      other e ∈ E ∧ e.1 ≠ other e ∧
        (x e.1 = x (other e) ∨ y e.1 = y (other e)) :=
    Classical.choose_spec (hbadExists e)
  let toCollision (e : ↥(E \ F)) : ↥collisionPairs :=
    ⟨(e.1, other e), by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨(Finset.mem_sdiff.mp e.2).1,
        (hother e).1⟩, ?_⟩
      exact ⟨(hother e).2.1, (hother e).2.2⟩⟩
  have htoCollision : Function.Injective toCollision := by
    intro e f hef
    apply Subtype.ext
    exact congrArg Prod.fst (congrArg Subtype.val hef)
  have hbadCard : (E \ F).card ≤ collisionPairs.card := by
    rw [← Fintype.card_coe, ← Fintype.card_coe]
    exact Fintype.card_le_of_injective toCollision htoCollision
  refine ⟨F, hFE, hxinj, hyinj, ?_⟩
  change E.card ≤ F.card + collisionPairs.card
  have hsplit := Finset.card_sdiff_add_card_eq_card hFE
  omega
