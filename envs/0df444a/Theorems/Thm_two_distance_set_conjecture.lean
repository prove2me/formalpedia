-- Prove2me | Theorems.Thm_two_distance_set_conjecture
-- name    : two_distance_set_conjecture
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T03:17:56.464624+00:00
-- url     : https://prove2.me/theorems/14ef736e-b2a8-4364-a74e-d06f82506c73
-- statement:
--   Two-distance set bound: A set in ℝᵈ with exactly 2 distinct pairwise distances has at most C(d+2,2) points. Proved by Einhorn-Schoenberg (1966); Delsarte's method achieves the bound. Extensions to s-distance sets remain open.
-- source:
--   https://en.wikipedia.org/wiki/Two-distance_set

import Mathlib

import Mathlib

theorem two_distance_set_conjecture (d : ℕ) (hd : 1 ≤ d) :
    ∀ (S : Finset (EuclideanSpace ℝ (Fin d))),
      (∃ alpha beta : ℝ, alpha ≠ beta ∧ 0 < alpha ∧ 0 < beta ∧
        ∀ x ∈ S, ∀ y ∈ S, x ≠ y → dist x y = alpha ∨ dist x y = beta) →
      S.card ≤ Nat.choose (d + 2) 2 := by
  sorry
