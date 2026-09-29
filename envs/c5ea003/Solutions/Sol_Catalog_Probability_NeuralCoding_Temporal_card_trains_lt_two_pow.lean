-- Prove2me | solution 1 for Catalog.Probability.NeuralCoding.Temporal.card_trains_lt_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T07:41:06.176901+00:00
-- url     : https://prove2.me/submissions/c7a786b9-70ff-4314-8676-71e48678bf7d

import Mathlib
import Definitions.Def_Probability_RefractorySpikeTrains
open Catalog.Probability.NeuralCoding.Temporal in
theorem solution (n : ℕ) (hn : 2 ≤ n) : (trains n).card < 2 ^ n := by
  -- the refractory recursion gives at most a Fibonacci-style bound
  have hle : ∀ m, (trains m).card ≤ 2 ^ m := by
    intro m
    induction m using Nat.twoStepInduction with
    | zero => simp [trains]
    | one => simp [trains]
    | more k ih1 ih2 =>
      have hstep : (trains (k + 2)).card ≤ (trains (k + 1)).card + (trains k).card := by
        simp only [trains]
        exact le_trans (Finset.card_union_le _ _)
          (add_le_add Finset.card_image_le Finset.card_image_le)
      have e1 : 2 ^ (k + 1) = 2 ^ k * 2 := by ring
      have e2 : 2 ^ (k + 2) = 2 ^ k * 4 := by ring
      omega
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hstep : (trains (m + 2)).card ≤ (trains (m + 1)).card + (trains m).card := by
    simp only [trains]
    exact le_trans (Finset.card_union_le _ _)
      (add_le_add Finset.card_image_le Finset.card_image_le)
  have h1 := hle (m + 1)
  have h2 := hle m
  have hp : 0 < 2 ^ m := Nat.two_pow_pos m
  have e1 : 2 ^ (m + 1) = 2 ^ m * 2 := by ring
  have e2 : 2 ^ (m + 2) = 2 ^ m * 4 := by ring
  omega
