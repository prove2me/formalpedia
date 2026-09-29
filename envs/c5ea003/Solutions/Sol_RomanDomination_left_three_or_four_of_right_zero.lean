-- Prove2me | solution 1 for RomanDomination.left_three_or_four_of_right_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T14:38:42.220621+00:00
-- url     : https://prove2.me/submissions/61920592-ea0f-4686-aa78-f5cedfd7ffad

import Mathlib
import Definitions.Def_Geometry_RomanDomination_ConvexBipartite
import Definitions.Def_Geometry_RomanDomination_DoubleRoman
import Definitions.Def_Geometry_RomanDomination_Variants
open RomanDomination Finset in
theorem solution {m n : ℕ} {f : Fin m ⊕ Fin n → ℕ} (hf : IsDRDF (K m n) f) {j : Fin n}
    (h0 : f (Sum.inr j) = 0) :
    (∃ i, f (Sum.inl i) = 3) ∨ 4 ≤ ∑ i, f (Sum.inl i) := by
  rcases hf.2.1 (Sum.inr j) h0 with ⟨u, hadj, hu⟩ | ⟨u, w, huw, hu, hw, hu2, hw2⟩
  · -- a neighbour labelled `3`, necessarily on the left
    cases u with
    | inl i => exact Or.inl ⟨i, hu⟩
    | inr j' => simp at hadj
  · -- two distinct left neighbours labelled `≥ 2`
    cases u with
    | inr j' => simp at hu
    | inl i₁ =>
      cases w with
      | inr j' => simp at hw
      | inl i₂ =>
        right
        have hne : i₁ ≠ i₂ := fun h => huw (by rw [h])
        calc 4 ≤ f (Sum.inl i₁) + f (Sum.inl i₂) := by omega
          _ = ∑ i ∈ {i₁, i₂}, f (Sum.inl i) := by rw [Finset.sum_pair hne]
          _ ≤ ∑ i, f (Sum.inl i) := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
