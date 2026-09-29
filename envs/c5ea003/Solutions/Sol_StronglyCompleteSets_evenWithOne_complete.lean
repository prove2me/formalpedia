-- Prove2me | solution 1 for StronglyCompleteSets.evenWithOne_complete
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:37:11.835193+00:00
-- url     : https://prove2.me/submissions/96b6aa17-f2d1-4912-9875-e3ef8b27f459

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
theorem solution: Complete evenWithOne := by
  use 0
  intro n _hn
  -- Case analysis: either n is even or n is odd
  by_cases heven : Even n
  · -- n is even: use singleton {n} (or empty set if n = 0)
    refine ⟨{n}, ?_, ?_⟩
    · simp [evenWithOne]; right; exact heven
    · simp
  · -- n is odd: use {1, n-1} where n-1 is even
    have hn_pos : n ≥ 1 := Nat.pos_of_ne_zero (fun h => heven (h.symm ▸ by decide))
    have hn1_even : Even (n - 1) := by
      rw [Nat.even_sub hn_pos]
      simp [heven]
    have hne : 1 ≠ n - 1 := by
      intro h
      have : n = 2 := by omega
      exact heven (this ▸ even_two)
    refine ⟨{1, n - 1}, ?_, ?_⟩
    · intro x hx
      rw [evenWithOne]
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff] at hx ⊢
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · right; rfl
      · left; exact hn1_even
    · rw [Finset.sum_pair hne]; simp [hn_pos]
