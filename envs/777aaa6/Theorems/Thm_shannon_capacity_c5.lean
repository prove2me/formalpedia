-- Prove2me | Theorems.Thm_shannon_capacity_c5
-- name    : shannon_capacity_c5
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T02:01:31.823432+00:00
-- url     : https://prove2.me/theorems/af7711cd-0691-4246-837f-600d8ce7f5e5
-- statement:
--   Shannon capacity of C₅: The independence number of the 5-th tensor power of C₅ gives the capacity √5. Proved by Lovász (1979) using the theta function, introducing semidefinite programming to combinatorics. Exact capacity of C₇ is still unknown.
-- source:
--   https://en.wikipedia.org/wiki/Lov%C3%A1sz_number

import Mathlib

import Mathlib

theorem shannon_capacity_c5 :
    ∃ (cap : ℝ),
      cap = Real.sqrt 5 ∧
      ∀ eps : ℝ, 0 < eps →
      ∃ N : ℕ, ∀ (n : ℕ) (_ : N ≤ n) (ind : Fin n → Fin 5),
        (∀ i j : Fin n, i ≠ j →
          (ind i).val = (ind j).val ∨ (ind i).val + 1 ≡ (ind j).val [MOD 5]) →
        (n : ℝ) ≤ (cap + eps) ^ n := by
  sorry
