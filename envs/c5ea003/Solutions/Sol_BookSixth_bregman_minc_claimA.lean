-- Prove2me | solution 1 for BookSixth.bregman_minc_claimA
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T11:20:11.263328+00:00
-- url     : https://prove2.me/submissions/7aa6e46b-7a24-48cd-afbc-a53e9e58e1c8

import Mathlib
import Definitions.Def_BregmanMincWeights
import Theorems.Thm_BookSixth_bregman_minc_path_expansion

open scoped BigOperators
open BregmanMincWeights

private noncomputable def completionMass {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℕ) : List (Fin n) → Finset (Fin n) → ℝ
  | [], _ => 1
  | i :: rows, unused =>
      (∑ j ∈ unused.filter (fun j => A i j = 1), completionMass A rows (unused.erase j)) /
        ((unused.filter (fun j => A i j = 1)).card : ℝ)

private theorem completionMass_le_one {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℕ) (rows : List (Fin n))
    (unused : Finset (Fin n)) : completionMass A rows unused ≤ 1 := by
  classical
  induction rows generalizing unused with
  | nil => simp [completionMass]
  | cons i rows ih =>
      let choices := unused.filter (fun j => A i j = 1)
      change (∑ j ∈ choices, completionMass A rows (unused.erase j)) /
        (choices.card : ℝ) ≤ 1
      by_cases h : choices.card = 0
      · simp [h]
      · have hpos : (0 : ℝ) < choices.card := by
          exact_mod_cast Nat.pos_of_ne_zero h
        apply (div_le_one hpos).2
        calc
          (∑ j ∈ choices, completionMass A rows (unused.erase j)) ≤
              ∑ _j ∈ choices, (1 : ℝ) :=
            Finset.sum_le_sum (fun j _ => ih (unused.erase j))
          _ = (choices.card : ℝ) := by simp

theorem solution : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℕ)
    (hA : ∀ i j, A i j ≤ 1) (hrows : ∀ i, 0 < ∑ j, A i j)
    (π : Equiv.Perm (Fin n)), ∑ σ ∈ aSys A, qW A σ π ≤ 1 := by
  classical
  intro n A hA hrows π
  have hexpand := BookSixth.bregman_minc_path_expansion n A π (completionMass A)
    (fun _ => rfl) (fun _ _ _ => rfl)
  rw [hexpand]
  exact completionMass_le_one A _ _
