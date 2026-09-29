-- Prove2me | solution 1 for VectorSpaceOpt.eidelheit_separation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-26T12:48:00.92288+00:00
-- url     : https://prove2.me/submissions/00f94242-35df-4f92-aaa5-f058f448866b

import Mathlib


theorem solution {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K₁ K₂ : Set X) (h₁ : Convex ℝ K₁) (h₂ : Convex ℝ K₂)
    (hKi : (interior K₁).Nonempty) (hne : K₂.Nonempty)
    (hdisj : K₂ ∩ interior K₁ = ∅) :
    ∃ (f : X →L[ℝ] ℝ) (c : ℝ), f ≠ 0 ∧ (∀ k ∈ K₁, f k ≤ c) ∧
      (∀ k ∈ K₂, c ≤ f k) := by
  have hd : Disjoint (interior K₁) K₂ := by
    rw [Set.disjoint_iff_inter_eq_empty, Set.inter_comm]; exact hdisj
  obtain ⟨f, u, hf0, hA, hB⟩ :=
    geometric_hahn_banach_of_nonempty_interior h₁ h₂ hd hKi hne
  exact ⟨f, u, hf0, hA, hB⟩
