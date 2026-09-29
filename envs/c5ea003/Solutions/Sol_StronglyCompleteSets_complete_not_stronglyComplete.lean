-- Prove2me | solution 1 for StronglyCompleteSets.complete_not_stronglyComplete
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:38:39.973177+00:00
-- url     : https://prove2.me/submissions/9c358d62-2619-4721-bfb2-1482cfb9838e

-- Sol generated from Logic/StronglyCompleteSets/Contrarian.lean
import Mathlib
import Definitions.Def_Logic_StronglyCompleteSets_Contrarian
import Theorems.Thm_StronglyCompleteSets_evenWithOne_complete

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
theorem solution:
    Complete evenWithOne ∧ ¬ StronglyComplete evenWithOne := by
  refine ⟨evenWithOne_complete, ?_⟩
  intro h
  -- If evenWithOne were strongly complete, then evenWithOne \ {1} would be complete
  have h1 : Complete (evenWithOne \ {1}) := h {1} (Set.finite_singleton 1)
  -- But evenWithOne \ {1} contains only even numbers
  -- Any sum of even numbers is even, so no odd number can be represented
  obtain ⟨N, hN⟩ := h1
  -- Find an odd number >= N
  let m := 2 * N + 1
  have hm_odd : Odd m := ⟨N, rfl⟩
  have hm_ge : m ≥ N := by omega
  have hm3 : IsSubsetSum (evenWithOne \ {1}) m := hN m hm_ge
  obtain ⟨s, hs_sub, hs_sum⟩ := hm3
  -- Every element in s is even
  have hall_even : ∀ a ∈ s, Even a := by
    intro a ha
    have hmem : a ∈ evenWithOne \ {1} := hs_sub ha
    rw [Set.mem_diff] at hmem
    rcases hmem with ⟨hmem1, hmem2⟩
    simp [evenWithOne] at hmem1
    tauto
  -- Sum of even numbers is even
  have hsum_even : Even (∑ a ∈ s, a) := by
    apply Finset.even_sum
    exact hall_even
  rw [hs_sum] at hsum_even
  exact Nat.not_even_iff_odd.mpr hm_odd hsum_even
