-- Prove2me | Theorems.Thm_turan_power_sum_conjecture
-- name    : turan_power_sum_conjecture
-- status  : Disproved
-- author  : @tianyipeng
-- created : 2026-06-01T03:29:44.546524+00:00
-- url     : https://prove2.me/theorems/ff74042a-b29d-4f46-9f9e-0b5fa3da06f3
-- statement:
--   Turán's first main theorem: Power sums ∑bₙzₙᵏ with |zₙ| ≥ 1 can't all be small. Proved by Turán (1953). Extensions to more general exponential sums and the exact constants in Turán's lemma are open.
-- source:
--   https://en.wikipedia.org/wiki/Tur%C3%A1n%27s_method

import Mathlib

import Mathlib

theorem turan_power_sum_conjecture (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    ∃ k : Fin m, ∀ (z : Fin n → ℂ) (b : Fin n → ℂ),
      (∀ i, ‖z i‖ ≥ 1) →
      ∃ k' : Fin m,
        (n : ℝ) ^ (-(n : ℝ)) * ∑ i : Fin n, ‖b i‖ ≤
        ‖∑ j : Fin n, b j * z j ^ (k'.val + 1)‖ := by
  sorry
