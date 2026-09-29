-- Prove2me | solution 1 for RomanDomination.six_le_weight_of_left_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T14:57:41.579977+00:00
-- url     : https://prove2.me/submissions/692f9acb-1640-44de-89e5-2229d6e455c1

import Mathlib
import Definitions.Def_Geometry_RomanDomination_ConvexBipartite
import Definitions.Def_Geometry_RomanDomination_DoubleRoman
import Definitions.Def_Geometry_RomanDomination_Variants
open RomanDomination Finset in
theorem solution {m n : ℕ} {f : Fin m ⊕ Fin n → ℕ} (hn : 3 ≤ n) (hf : IsDRDF (K m n) f)
    (ha : 2 ≤ ∑ i, f (Sum.inl i)) (h0 : ∃ i, f (Sum.inl i) = 0) : 6 ≤ weight f := by
  have hw : weight f = ∑ i, f (Sum.inl i) + ∑ j, f (Sum.inr j) := Fintype.sum_sum_type f
  have singleL : ∀ i, f (Sum.inl i) ≤ ∑ i, f (Sum.inl i) := fun i =>
    Finset.single_le_sum (f := fun i => f (Sum.inl i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have pairL : ∀ a b : Fin m, a ≠ b → f (Sum.inl a) + f (Sum.inl b) ≤ ∑ i, f (Sum.inl i) := by
    intro a b hab
    rw [← Finset.sum_pair (f := fun i => f (Sum.inl i)) hab]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have pairR : ∀ a b : Fin n, a ≠ b → f (Sum.inr a) + f (Sum.inr b) ≤ ∑ j, f (Sum.inr j) := by
    intro a b hab
    rw [← Finset.sum_pair (f := fun j => f (Sum.inr j)) hab]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  obtain ⟨i, hi⟩ := h0
  rcases hf.2.1 (Sum.inl i) hi with ⟨u, hadj, hu⟩ | ⟨u, w, huw, hu, hw', hu2, hw2⟩
  · cases u with
    | inl i' => simp at hadj
    | inr j =>
      -- a right `3`; if the left labels sum to exactly `2`, a second right label is nonzero
      by_cases hA3 : 3 ≤ ∑ i, f (Sum.inl i)
      · have : f (Sum.inr j) ≤ ∑ j, f (Sum.inr j) :=
          Finset.single_le_sum (f := fun j => f (Sum.inr j)) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ j)
        omega
      · obtain ⟨r, hr⟩ := Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) j
        have hr0 : f (Sum.inr r) ≠ 0 := by
          intro hr0
          rcases hf.2.1 (Sum.inr r) hr0 with ⟨u, hadj, hu⟩ | ⟨u, w, huw, hu, hw', hu2, hw2⟩
          · cases u with
            | inl i' => have := singleL i'; omega
            | inr j' => simp at hadj
          · cases u with
            | inr j' => simp at hu
            | inl i₁ =>
              cases w with
              | inr j' => simp at hw'
              | inl i₂ =>
                have := pairL i₁ i₂ (fun h => huw (by rw [h]))
                omega
        have := pairR r j hr
        omega
  · cases u with
    | inl i' => simp at hu
    | inr j₁ =>
      cases w with
      | inl i' => simp at hw'
      | inr j₂ =>
        have := pairR j₁ j₂ (fun h => huw (by rw [h]))
        omega
