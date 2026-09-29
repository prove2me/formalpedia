-- Prove2me | solution 1 for mme_finset_two_mode_collision_pairs_card_le_of_fiber_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T00:16:35.760274+00:00
-- url     : https://prove2.me/submissions/3f04e4d7-bda4-4495-a21a-62a51150db84

import Mathlib

set_option autoImplicit false

/-- The ordered distinct pairs sharing either of two labels are bounded by
twice the number of vertices times a uniform label-fiber degree. -/
theorem solution
    {α β γ : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (E : Finset α) (x : α → β) (y : α → γ) (D : ℕ)
    (hx : ∀ a ∈ E, (E.filter (fun b => x b = x a)).card ≤ D)
    (hy : ∀ a ∈ E, (E.filter (fun b => y b = y a)).card ≤ D) :
    ((E.product E).filter (fun p =>
      p.1 ≠ p.2 ∧ (x p.1 = x p.2 ∨ y p.1 = y p.2))).card ≤
        2 * E.card * D := by
  let C := (E.product E).filter (fun p =>
    p.1 ≠ p.2 ∧ (x p.1 = x p.2 ∨ y p.1 = y p.2))
  let Cx := (E.product E).filter (fun p => x p.1 = x p.2)
  let Cy := (E.product E).filter (fun p => y p.1 = y p.2)
  have hsub : C ⊆ Cx ∪ Cy := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    rcases hp'.2.2 with hpx | hpy
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp'.1, hpx⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp'.1, hpy⟩)
  have hCx : Cx.card ≤ E.card * D := by
    change ((E.product E).filter (fun p => x p.1 = x p.2)).card ≤ _
    rw [Finset.card_filter]
    change (∑ i ∈ E ×ˢ E, if x i.1 = x i.2 then 1 else 0) ≤ _
    rw [Finset.sum_product]
    calc
      (∑ a ∈ E, ∑ b ∈ E, if x a = x b then 1 else 0) =
          ∑ a ∈ E, (E.filter (fun b => x b = x a)).card := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.card_filter]
        apply Finset.sum_congr rfl
        intro b hb
        by_cases h : x a = x b
        · rw [if_pos h, if_pos h.symm]
        · rw [if_neg h, if_neg (fun hba => h hba.symm)]
      _ ≤ ∑ _a ∈ E, D := by
        exact Finset.sum_le_sum hx
      _ = E.card * D := by simp
  have hCy : Cy.card ≤ E.card * D := by
    change ((E.product E).filter (fun p => y p.1 = y p.2)).card ≤ _
    rw [Finset.card_filter]
    change (∑ i ∈ E ×ˢ E, if y i.1 = y i.2 then 1 else 0) ≤ _
    rw [Finset.sum_product]
    calc
      (∑ a ∈ E, ∑ b ∈ E, if y a = y b then 1 else 0) =
          ∑ a ∈ E, (E.filter (fun b => y b = y a)).card := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.card_filter]
        apply Finset.sum_congr rfl
        intro b hb
        by_cases h : y a = y b
        · rw [if_pos h, if_pos h.symm]
        · rw [if_neg h, if_neg (fun hba => h hba.symm)]
      _ ≤ ∑ _a ∈ E, D := by
        exact Finset.sum_le_sum hy
      _ = E.card * D := by simp
  calc
    C.card ≤ (Cx ∪ Cy).card := Finset.card_le_card hsub
    _ ≤ Cx.card + Cy.card := Finset.card_union_le _ _
    _ ≤ E.card * D + E.card * D := Nat.add_le_add hCx hCy
    _ = 2 * E.card * D := by ring
