-- Prove2me | Theorems.Thm_green_tao_theorem
-- name    : green_tao_theorem
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T02:01:54.454926+00:00
-- url     : https://prove2.me/theorems/253207cf-5565-4904-bb42-d9e1783fb0c3
-- statement:
--   Green–Tao theorem (2004): The prime numbers contain arithmetic progressions of arbitrary length. A landmark result combining Szemerédi's theorem with analytic number theory techniques. One of the most celebrated theorems of the 21st century.
-- source:
--   https://en.wikipedia.org/wiki/Green%E2%80%93Tao_theorem

import Mathlib

import Mathlib

theorem green_tao_theorem (k : ℕ) (hk : 1 ≤ k) :
    ∃ a d : ℕ, 1 ≤ d ∧ ∀ j : Fin k, Nat.Prime (a + j.val * d) := by
  sorry
