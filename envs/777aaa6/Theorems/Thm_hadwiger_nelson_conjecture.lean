-- Prove2me | Theorems.Thm_hadwiger_nelson_conjecture
-- name    : hadwiger_nelson_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T19:37:13.939207+00:00
-- url     : https://prove2.me/theorems/f98750b8-e73b-4659-b3bc-b4ea3788fa2c
-- statement:
--   The Hadwiger-Nelson problem (chromatic number of the plane): What is the minimum number of colors needed to color every point of R^2 so no two unit-distance points share a color? Lower bound 5 (de Grey 2018), upper bound 7. The exact value in {5,6,7} is unknown.
-- source:
--   https://en.wikipedia.org/wiki/Hadwiger-Nelson_problem

import Mathlib

import Mathlib

-- Hadwiger-Nelson problem: chromatic number of ℝ² with unit distances
-- The minimum k such that ℝ² can be k-colored with no two same-colored unit-distance points
-- is in {5,6,7}: lower bound 5 (de Grey 2018), upper bound 7 (Isbell 1950)
theorem hadwiger_nelson_conjecture : ∃ k ∈ ({5, 6, 7} : Finset ℕ),
    (∃ col : ℝ × ℝ → Fin k,
      ∀ p q : ℝ × ℝ, (p.1 - q.1)^2 + (p.2 - q.2)^2 = 1 → col p ≠ col q) ∧
    (∀ j : ℕ, j < k → ∀ col : ℝ × ℝ → Fin j,
      ∃ p q : ℝ × ℝ, (p.1 - q.1)^2 + (p.2 - q.2)^2 = 1 ∧ col p = col q) := by
  sorry
