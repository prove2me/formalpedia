-- Prove2me | solution 1 for RomanDomination.six_le_weight_of_isDRDF_K
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T20:07:28.518073+00:00
-- url     : https://prove2.me/submissions/74cd9eb4-efae-4f52-b956-efee4f6a64a2

import Mathlib
import Definitions.Def_Geometry_RomanDomination_ConvexBipartite
import Definitions.Def_Geometry_RomanDomination_DoubleRoman
import Definitions.Def_Geometry_RomanDomination_Variants
open RomanDomination Finset in
theorem solution {m n : ℕ} {f : Fin m ⊕ Fin n → ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n)
    (hf : IsDRDF (K m n) f) : 6 ≤ weight f := by
  -- left labels summing to `≤ 1` force every right label `≥ 2`
  have h3 : ∑ i, f (Sum.inl i) ≤ 1 → 6 ≤ weight f := by
    intro ha
    -- every left label is at most `1`
    have hle : ∀ i, f (Sum.inl i) ≤ 1 := fun i =>
      (Finset.single_le_sum (f := fun i => f (Sum.inl i)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)).trans ha
    -- so no right vertex can be labelled `0` or `1`: its neighbours are all on the left
    have hright : ∀ j, 2 ≤ f (Sum.inr j) := by
      intro j
      by_contra hlt
      push Not at hlt
      rcases Nat.lt_succ_iff.mp hlt |>.lt_or_eq with h0 | h1
      · have h0' : f (Sum.inr j) = 0 := by omega
        rcases hf.2.1 (Sum.inr j) h0' with ⟨u, hadj, hu⟩ | ⟨u, w, -, hu, -, hu2, -⟩
        · cases u with
          | inl i => have := hle i; omega
          | inr j' => simp at hadj
        · cases u with
          | inl i => have := hle i; omega
          | inr j' => simp at hu
      · obtain ⟨u, hadj, hu⟩ := hf.2.2 (Sum.inr j) h1
        cases u with
        | inl i => have := hle i; omega
        | inr j' => simp at hadj
    have hB : 2 * n ≤ ∑ j, f (Sum.inr j) := by
      calc 2 * n = ∑ _j : Fin n, 2 := by simp [mul_comm]
        _ ≤ ∑ j, f (Sum.inr j) := Finset.sum_le_sum fun j _ => hright j
    have hw : weight f = ∑ i, f (Sum.inl i) + ∑ j, f (Sum.inr j) := Fintype.sum_sum_type f
    omega
  -- right labels summing to `≤ 1` force every left label `≥ 2`
  have h4 : ∑ j, f (Sum.inr j) ≤ 1 → 6 ≤ weight f := by
    intro hb
    -- every right label is at most `1`
    have hle : ∀ j, f (Sum.inr j) ≤ 1 := fun j =>
      (Finset.single_le_sum (f := fun j => f (Sum.inr j)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)).trans hb
    -- so no left vertex can be labelled `0` or `1`: its neighbours are all on the right
    have hleft : ∀ i, 2 ≤ f (Sum.inl i) := by
      intro i
      by_contra hlt
      push Not at hlt
      rcases Nat.lt_succ_iff.mp hlt |>.lt_or_eq with h0 | h1
      · have h0' : f (Sum.inl i) = 0 := by omega
        rcases hf.2.1 (Sum.inl i) h0' with ⟨u, hadj, hu⟩ | ⟨u, w, -, hu, -, hu2, -⟩
        · cases u with
          | inl i' => simp at hadj
          | inr j => have := hle j; omega
        · cases u with
          | inl i' => simp at hu
          | inr j => have := hle j; omega
      · obtain ⟨u, hadj, hu⟩ := hf.2.2 (Sum.inl i) h1
        cases u with
        | inl i' => simp at hadj
        | inr j => have := hle j; omega
    have hA : 2 * m ≤ ∑ i, f (Sum.inl i) := by
      calc 2 * m = ∑ _i : Fin m, 2 := by simp [mul_comm]
        _ ≤ ∑ i, f (Sum.inl i) := Finset.sum_le_sum fun i _ => hleft i
    have hw : weight f = ∑ i, f (Sum.inl i) + ∑ j, f (Sum.inr j) := Fintype.sum_sum_type f
    omega
  -- a left `0` with left sum `≥ 2`
  have h6 : 2 ≤ ∑ i, f (Sum.inl i) → (∃ i, f (Sum.inl i) = 0) → 6 ≤ weight f := by
    intro ha h0
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
  -- no left `0` with right sum `≥ 2`
  have h7 : 2 ≤ ∑ j, f (Sum.inr j) → (∀ i, f (Sum.inl i) ≠ 0) → 6 ≤ weight f := by
    intro hb h0
    have hw : weight f = ∑ i, f (Sum.inl i) + ∑ j, f (Sum.inr j) := Fintype.sum_sum_type f
    by_cases hA4 : 4 ≤ ∑ i, f (Sum.inl i)
    · omega
    · -- left sum `≤ 3` with `m ≥ 3` nonzero labels: every left label is `1`
      have hle : ∀ i, f (Sum.inl i) ≤ 1 := by
        intro i
        have hsplit := Finset.add_sum_erase Finset.univ (fun i => f (Sum.inl i)) (Finset.mem_univ i)
        have hrest : m - 1 ≤ ∑ i' ∈ Finset.univ.erase i, f (Sum.inl i') := by
          calc m - 1 = ∑ _i' ∈ Finset.univ.erase i, 1 := by
                rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_erase_of_mem (Finset.mem_univ i),
                  Finset.card_univ, Fintype.card_fin]
            _ ≤ ∑ i' ∈ Finset.univ.erase i, f (Sum.inl i') :=
                Finset.sum_le_sum fun i' _ => Nat.one_le_iff_ne_zero.mpr (h0 i')
        simp only at hsplit
        omega
      -- hence every right label is at least `2`
      have hright : ∀ j, 2 ≤ f (Sum.inr j) := by
        intro j
        by_contra hlt
        push Not at hlt
        rcases Nat.lt_succ_iff.mp hlt |>.lt_or_eq with h0' | h1
        · have h0'' : f (Sum.inr j) = 0 := by omega
          rcases hf.2.1 (Sum.inr j) h0'' with ⟨u, hadj, hu⟩ | ⟨u, w, -, hu, -, hu2, -⟩
          · cases u with
            | inl i => have := hle i; omega
            | inr j' => simp at hadj
          · cases u with
            | inl i => have := hle i; omega
            | inr j' => simp at hu
        · obtain ⟨u, hadj, hu⟩ := hf.2.2 (Sum.inr j) h1
          cases u with
          | inl i => have := hle i; omega
          | inr j' => simp at hadj
      have hB : 2 * n ≤ ∑ j, f (Sum.inr j) := by
        calc 2 * n = ∑ _j : Fin n, 2 := by simp [mul_comm]
          _ ≤ ∑ j, f (Sum.inr j) := Finset.sum_le_sum fun j _ => hright j
      omega
  by_cases hA : ∑ i, f (Sum.inl i) ≤ 1
  · exact h3 hA
  by_cases hB : ∑ j, f (Sum.inr j) ≤ 1
  · exact h4 hB
  by_cases hz : ∃ i, f (Sum.inl i) = 0
  · exact h6 (by omega) hz
  · push Not at hz
    exact h7 (by omega) hz
