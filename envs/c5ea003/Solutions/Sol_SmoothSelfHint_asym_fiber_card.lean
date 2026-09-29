-- Prove2me | solution 1 for SmoothSelfHint.asym_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T08:36:14.594178+00:00
-- url     : https://prove2.me/submissions/50a6c238-ca64-4841-a8c9-807b1c750e5a

import Mathlib
import Definitions.Def_Tropical_SmoothSelfHintDichotomyCore
open SmoothSelfHint in
theorem solution {G : Type*} [Group G] [Fintype G] [DecidableEq G] (A : Finset G) (n : G) :
    (asymFiber A n).card = A.card := by
  classical
  have h : asymFiber A n = A.image (fun a => (a, a⁻¹ * n)) := by
    ext ab
    obtain ⟨a, b⟩ := ab
    simp only [asymFiber, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Prod.mk.injEq]
    constructor
    · rintro ⟨hab, ha⟩
      refine ⟨a, ha, rfl, ?_⟩
      rw [← hab]
      group
    · rintro ⟨a', ha', rfl, rfl⟩
      exact ⟨by group, ha'⟩
  rw [h, Finset.card_image_of_injective]
  intro x y hxy
  exact (Prod.mk.injEq _ _ _ _).mp hxy |>.1
