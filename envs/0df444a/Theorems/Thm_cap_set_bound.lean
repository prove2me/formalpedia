-- Prove2me | Theorems.Thm_cap_set_bound
-- name    : cap_set_bound
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T01:59:25.853575+00:00
-- url     : https://prove2.me/theorems/f0fd7615-b07c-4d4f-8791-397e176112db
-- statement:
--   Cap set problem (proved by Ellenberg–Gijswijt 2016): The maximum size of a subset of 𝔽₃ⁿ with no 3-term arithmetic progression is O(2.756ⁿ). A breakthrough in combinatorics resolving a decades-old conjecture.
-- source:
--   https://en.wikipedia.org/wiki/Cap_set

import Mathlib

import Mathlib

theorem cap_set_bound (n : ℕ) (hn : 1 ≤ n)
    (A : Finset (Fin n → ZMod 3))
    (hcap : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = 0 → x = y) :
    (A.card : ℝ) ≤ 2.756 ^ n := by
  sorry
