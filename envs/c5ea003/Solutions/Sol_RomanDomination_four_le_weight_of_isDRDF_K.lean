-- Prove2me | solution 1 for RomanDomination.four_le_weight_of_isDRDF_K
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T14:53:11.92868+00:00
-- url     : https://prove2.me/submissions/6859cf15-d490-4c87-9a74-1030b915c8b6

import Mathlib
import Definitions.Def_Geometry_RomanDomination_ConvexBipartite
import Definitions.Def_Geometry_RomanDomination_DoubleRoman
import Definitions.Def_Geometry_RomanDomination_Variants
open RomanDomination Finset in
theorem solution {m n : ℕ} {f : Fin m ⊕ Fin n → ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hf : IsDRDF (K m n) f) : 4 ≤ weight f := by
  have hw : weight f = ∑ i, f (Sum.inl i) + ∑ j, f (Sum.inr j) := Fintype.sum_sum_type f
  have singleL : ∀ i, f (Sum.inl i) ≤ ∑ i, f (Sum.inl i) := fun i =>
    Finset.single_le_sum (f := fun i => f (Sum.inl i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have singleR : ∀ j, f (Sum.inr j) ≤ ∑ j, f (Sum.inr j) := fun j =>
    Finset.single_le_sum (f := fun j => f (Sum.inr j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have pairL : ∀ a b : Fin m, a ≠ b → f (Sum.inl a) + f (Sum.inl b) ≤ ∑ i, f (Sum.inl i) := by
    intro a b hab
    rw [← Finset.sum_pair (f := fun i => f (Sum.inl i)) hab]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  by_cases hA0 : ∃ i, f (Sum.inl i) = 0
  · obtain ⟨i, hi⟩ := hA0
    rcases hf.2.1 (Sum.inl i) hi with ⟨u, hadj, hu⟩ | ⟨u, w, huw, hu, hw', hu2, hw2⟩
    · cases u with
      | inl i' => simp at hadj
      | inr j =>
        have hB3 := singleR j
        by_cases hA1 : 1 ≤ ∑ i, f (Sum.inl i)
        · omega
        · -- all left labels vanish, so every right label is at least `2`
          have hle : ∀ i, f (Sum.inl i) = 0 := fun i => by have := singleL i; omega
          have hright : ∀ j, 2 ≤ f (Sum.inr j) := by
            intro j
            by_contra hlt
            push Not at hlt
            rcases Nat.lt_succ_iff.mp hlt |>.lt_or_eq with h0 | h1
            · have h0' : f (Sum.inr j) = 0 := by omega
              rcases hf.2.1 (Sum.inr j) h0' with ⟨u, hadj, hu⟩ | ⟨u, w, -, hu, -, hu2, -⟩
              · cases u with
                | inl i => rw [hle i] at hu; omega
                | inr j' => simp at hadj
              · cases u with
                | inl i => rw [hle i] at hu2; omega
                | inr j' => simp at hu
            · obtain ⟨u, hadj, hu⟩ := hf.2.2 (Sum.inr j) h1
              cases u with
              | inl i => rw [hle i] at hu; omega
              | inr j' => simp at hadj
          have hB : 2 * n ≤ ∑ j, f (Sum.inr j) := by
            calc 2 * n = ∑ _j : Fin n, 2 := by simp [mul_comm]
              _ ≤ ∑ j, f (Sum.inr j) := Finset.sum_le_sum fun j _ => hright j
          omega
    · cases u with
      | inl i' => simp at hu
      | inr j₁ =>
        cases w with
        | inl i' => simp at hw'
        | inr j₂ =>
          have hne : j₁ ≠ j₂ := fun h => huw (by rw [h])
          have : f (Sum.inr j₁) + f (Sum.inr j₂) ≤ ∑ j, f (Sum.inr j) := by
            rw [← Finset.sum_pair (f := fun j => f (Sum.inr j)) hne]
            exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
          omega
  · push Not at hA0
    have hA : m ≤ ∑ i, f (Sum.inl i) := by
      calc m = ∑ _i : Fin m, 1 := by simp
        _ ≤ ∑ i, f (Sum.inl i) := Finset.sum_le_sum fun i _ => Nat.one_le_iff_ne_zero.mpr (hA0 i)
    by_cases hB0 : ∃ j, f (Sum.inr j) = 0
    · obtain ⟨j, hj⟩ := hB0
      rcases hf.2.1 (Sum.inr j) hj with ⟨u, hadj, hu⟩ | ⟨u, w, huw, hu, hw', hu2, hw2⟩
      · cases u with
        | inl i =>
          -- a left `3` plus another nonzero left label
          obtain ⟨i', hi'⟩ := Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) i
          have := pairL i' i hi'
          have := Nat.one_le_iff_ne_zero.mpr (hA0 i')
          omega
        | inr j' => simp at hadj
      · cases u with
        | inr j' => simp at hu
        | inl i₁ =>
          cases w with
          | inr j' => simp at hw'
          | inl i₂ =>
            have := pairL i₁ i₂ (fun h => huw (by rw [h]))
            omega
    · push Not at hB0
      have hB : n ≤ ∑ j, f (Sum.inr j) := by
        calc n = ∑ _j : Fin n, 1 := by simp
          _ ≤ ∑ j, f (Sum.inr j) := Finset.sum_le_sum fun j _ => Nat.one_le_iff_ne_zero.mpr (hB0 j)
      omega
