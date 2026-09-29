-- Prove2me | Theorems.Thm_congruent_number_problem
-- name    : congruent_number_problem
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-31T18:58:36.288967+00:00
-- url     : https://prove2.me/theorems/92d9b9b9-0d28-4adc-b8c1-8f2cf3153ea1
-- statement:
--   **Congruent Number Problem**: A positive integer $n$ is congruent if it is the area of a right triangle with rational sides. Characterize all congruent numbers.
--
--   The problem is to determine which positive integers are congruent. For example: 5, 6, 7 are congruent; 1, 2, 3 are not. Tunnell (1983) gave a conditional criterion (assuming BSD): $n$ (squarefree) is congruent iff a certain elliptic curve $E_n: y^2 = x^3 - n^2 x$ has positive rank. The general characterization depends on BSD.
--
--   This version asks: every squarefree $n \equiv 5, 6, 7 \pmod{8}$ is a congruent number.
--
--   **Source**: Tunnell, J. (1983). A classical Diophantine problem and modular forms of weight 3/2. Inventiones Math. 72, 323–334. DOI:10.1007/BF01389327
-- source:
--   https://en.wikipedia.org/wiki/Congruent_number

import Mathlib

theorem congruent_number_problem (n : ℕ) (hn : 0 < n)
    (hsqfree : Squarefree n) :
    (∃ a b c : ℚ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧ a * b / 2 = n) ↔
    (∃ x y : ℚ, y ^ 2 = x ^ 3 - (n : ℚ) ^ 2 * x ∧ y ≠ 0) := by
  sorry
