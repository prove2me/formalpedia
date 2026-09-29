-- Prove2me | solution 1 for RomanDomination.right_three_or_four_of_left_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T14:34:22.992147+00:00
-- url     : https://prove2.me/submissions/b1bd5458-69d5-4dcb-b68d-1e88e572797b

import Mathlib
import Definitions.Def_Geometry_RomanDomination_ConvexBipartite
import Definitions.Def_Geometry_RomanDomination_DoubleRoman
import Definitions.Def_Geometry_RomanDomination_Variants
open RomanDomination Finset in
theorem solution {m n : ℕ} {f : Fin m ⊕ Fin n → ℕ} (hf : IsDRDF (K m n) f) {i : Fin m}
    (h0 : f (Sum.inl i) = 0) :
    (∃ j, f (Sum.inr j) = 3) ∨ 4 ≤ ∑ j, f (Sum.inr j) := by
  rcases hf.2.1 (Sum.inl i) h0 with ⟨u, hadj, hu⟩ | ⟨u, w, huw, hu, hw, hu2, hw2⟩
  · -- a neighbour labelled `3`, necessarily on the right
    cases u with
    | inl i' => simp at hadj
    | inr j => exact Or.inl ⟨j, hu⟩
  · -- two distinct right neighbours labelled `≥ 2`
    cases u with
    | inl i' => simp at hu
    | inr j₁ =>
      cases w with
      | inl i' => simp at hw
      | inr j₂ =>
        right
        have hne : j₁ ≠ j₂ := fun h => huw (by rw [h])
        calc 4 ≤ f (Sum.inr j₁) + f (Sum.inr j₂) := by omega
          _ = ∑ j ∈ {j₁, j₂}, f (Sum.inr j) := by rw [Finset.sum_pair hne]
          _ ≤ ∑ j, f (Sum.inr j) := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
