-- Prove2me | solution 1 for StronglyCompleteSets.stronglyComplete_congr_finite
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:38:40.500136+00:00
-- url     : https://prove2.me/submissions/7da3a34a-66a5-4be5-a96b-10c6efa7392e

-- Sol generated from Logic/StronglyCompleteSets/Contrarian.lean
import Mathlib
import Definitions.Def_Logic_StronglyCompleteSets_Contrarian

/-!
# Strongly complete sets: structural results and a counterexample

This file formalizes the basic notions from *Strongly complete sets and a conjecture
of Erdős*.  It then tests the tempting strengthening “every complete set is strongly
complete”.  The statement is false: the set consisting of all even natural numbers
together with `1` is complete, but deleting `1` leaves a parity obstruction.

We also prove that strong completeness is unchanged by a finite perturbation.  This
isolates the robustness built into the paper's definition.
-/

open StronglyCompleteSets












open StronglyCompleteSets in
theorem solution{A B : Set ℕ}
    (hAB : ((A \ B) ∪ (B \ A)).Finite) : StronglyComplete A ↔ StronglyComplete B := by
  have hFA : (A \ B).Finite := hAB.subset (Set.subset_union_left)
  have hFB : (B \ A).Finite := hAB.subset (Set.subset_union_right)
  constructor
  · intro hA G hG
    -- Need to show B \ G is complete
    -- C = (A ∩ B) \ G is complete (since A is SC, A \ (G ∪ (A \ B)) is complete)
    -- C ⊆ B \ G, so B \ G is complete
    have hC_A : Complete ((A ∩ B) \ G) := by
      have : (A ∩ B) \ G = A \ (G ∪ (A \ B)) := by ext x; simp [Set.mem_inter_iff, Set.mem_diff]; tauto
      rw [this]
      exact hA (G ∪ (A \ B)) (hG.union hFA)
    -- C ⊆ B \ G
    have hsup : (A ∩ B) \ G ⊆ B \ G := by
      intro x hx
      simp only [Set.mem_diff, Set.mem_inter_iff] at hx ⊢
      exact ⟨hx.1.2, hx.2⟩
    -- Complete sets are preserved under superset
    obtain ⟨N, hN⟩ := hC_A
    exact ⟨N, fun n hn => by
      obtain ⟨s, hs, hs_sum⟩ := hN n hn
      exact ⟨s, hs.trans hsup, hs_sum⟩⟩
  · intro hB G hG
    -- Need to show A \ G is complete
    -- C = (A ∩ B) \ G is complete (since B is SC, B \ (G ∪ (B \ A)) is complete)
    -- C ⊆ A \ G, so A \ G is complete
    have hC_B : Complete ((A ∩ B) \ G) := by
      have : (A ∩ B) \ G = B \ (G ∪ (B \ A)) := by ext x; simp [Set.mem_inter_iff, Set.mem_diff]; tauto
      rw [this]
      exact hB (G ∪ (B \ A)) (hG.union hFB)
    -- C ⊆ A \ G
    have hsup : (A ∩ B) \ G ⊆ A \ G := by
      intro x hx
      simp only [Set.mem_diff, Set.mem_inter_iff] at hx ⊢
      exact ⟨hx.1.1, hx.2⟩
    -- Complete sets are preserved under superset
    obtain ⟨N, hN⟩ := hC_B
    refine ⟨N, ?_⟩
    intro n hn
    obtain ⟨s, hs, hs_sum⟩ := hN n hn
    exact ⟨s, hs.trans hsup, hs_sum⟩
