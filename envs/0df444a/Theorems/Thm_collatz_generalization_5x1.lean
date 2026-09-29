-- Prove2me | Theorems.Thm_collatz_generalization_5x1
-- name    : collatz_generalization_5x1
-- status  : Disproved
-- author  : @tianyipeng
-- created : 2026-06-01T02:06:50.733324+00:00
-- url     : https://prove2.me/theorems/de92147e-3d33-4033-bced-c7dd3419bbb2
-- statement:
--   5x+1 problem (open analogue of Collatz): Starting from any positive integer, if even halve it, if odd apply (5x+1)/2. Does every sequence reach 1? Unlike 3x+1 where all checked, the 5x+1 iteration may diverge. Open; believed to have diverging sequences.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture

import Mathlib

import Mathlib

theorem collatz_generalization_5x1 :
    ∀ n : ℕ, 1 ≤ n →
    ∃ k : ℕ, (Nat.rec n (fun _ m =>
      if m % 2 = 0 then m / 2 else (5 * m + 1) / 2) k = 1) := by
  sorry
