-- Prove2me | solution 1 for TFoldSumsetAvoidance.dense_set_avoids_large_sumsets
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T15:46:23.58832+00:00
-- url     : https://prove2.me/submissions/b63c05f7-75e6-45d1-ad38-a1f4844a7823

import Mathlib
import Definitions.Def_Logic_PosetTheory_TFoldSumsetAvoidance

open Finset Pointwise TFoldSumsetAvoidance in
theorem solution (n t k : ℕ) (δ : ℝ) (hδ : δ ≤ 1)
    (hbarrier : n ≤ t * (k - 1)) :
    ∃ S : Finset ℤ, ((S : Finset ℤ) ⊆ (Finset.range n).image (Nat.cast : ℕ → ℤ)) ∧
      δ * n ≤ S.card ∧
      ∀ l : List (Finset ℤ), l.length = t → (∀ A ∈ l, A.Nonempty) →
        (∀ A ∈ l, k ≤ A.card) → ¬ sumsetList l ⊆ S := by
  -- iterated Cauchy–Davenport in `ℤ`
  have main : ∀ l : List (Finset ℤ), (∀ A ∈ l, A.Nonempty) → (∀ A ∈ l, k ≤ A.card) →
      (sumsetList l).Nonempty ∧ l.length * (k - 1) + 1 ≤ (sumsetList l).card := by
    intro l
    induction l with
    | nil =>
      intro _ _
      simp [sumsetList]
    | cons A l ih =>
      intro hne hk
      obtain ⟨hne', hcard⟩ := ih (fun B hB => hne B (List.mem_cons_of_mem A hB))
        (fun B hB => hk B (List.mem_cons_of_mem A hB))
      have hA : A.Nonempty := hne A List.mem_cons_self
      have hkA : k ≤ A.card := hk A List.mem_cons_self
      have hsum : sumsetList (A :: l) = A + sumsetList l := rfl
      have hcd := cauchy_davenport_add_of_linearOrder_isCancelAdd hA hne'
      have hA1 : 1 ≤ A.card := Finset.card_pos.2 hA
      refine ⟨hsum ▸ hA.add hne', ?_⟩
      rw [hsum, List.length_cons, add_mul, one_mul]
      omega
  refine ⟨(Finset.range n).image (Nat.cast : ℕ → ℤ), subset_rfl, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
    exact mul_le_of_le_one_left (Nat.cast_nonneg n) hδ
  · intro l hlen hne hk hsub
    obtain ⟨-, hcard⟩ := main l hne hk
    have hle := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range] at hle
    rw [hlen] at hcard
    omega
