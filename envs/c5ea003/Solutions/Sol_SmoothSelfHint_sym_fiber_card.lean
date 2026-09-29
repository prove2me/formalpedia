-- Prove2me | solution 1 for SmoothSelfHint.sym_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T06:42:58.483986+00:00
-- url     : https://prove2.me/submissions/32a5367c-39df-4d65-a5bc-f7573a2a97f3

import Mathlib
import Definitions.Def_Tropical_SmoothSelfHintDichotomyCore
open SmoothSelfHint Finset in
theorem solution {G : Type*} [Group G] [Fintype G] [DecidableEq G] (A : Finset G) (n : G) :
    (symFiber A n).card = (A ∪ A.image (fun b => n * b⁻¹)).card := by
  -- a pair `(a,b)` with `a*b = n` is determined by `a`, so project to the first coordinate
  refine Finset.card_bij' (fun ab _ => ab.1) (fun a _ => (a, a⁻¹ * n)) ?_ ?_ ?_ ?_
  · -- the first coordinate lands in `A ∪ n·A⁻¹`
    rintro ⟨a, b⟩ hab
    simp only [symFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hab
    obtain ⟨hprod, hmem⟩ := hab
    rcases hmem with ha | hb
    · exact Finset.mem_union_left _ ha
    · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b, hb, ?_⟩)
      -- `a * b = n` gives `a = n * b⁻¹`
      show n * b⁻¹ = a
      rw [← hprod, mul_inv_cancel_right]
  · -- conversely `a ↦ (a, a⁻¹ n)` lands in the fibre
    intro a ha
    simp only [symFiber, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨by rw [mul_inv_cancel_left], ?_⟩
    rcases Finset.mem_union.mp ha with ha' | ha'
    · exact Or.inl ha'
    · obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp ha'
      refine Or.inr ?_
      -- `a = n * b⁻¹` gives `a⁻¹ * n = b`
      have : a⁻¹ * n = b := by rw [← hab]; group
      rw [this]
      exact hb
  · -- round trip on the fibre: the second coordinate is recovered from `a*b = n`
    rintro ⟨a, b⟩ hab
    simp only [symFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hab
    have hprod := hab.1
    show ((a, b).1, (a, b).1⁻¹ * n) = (a, b)
    have hb2 : a⁻¹ * n = b := by rw [← hprod]; group
    simp [hb2]
  · -- round trip on the union
    intro a _
    rfl
