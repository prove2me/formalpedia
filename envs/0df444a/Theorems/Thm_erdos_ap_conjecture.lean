-- Prove2me | Theorems.Thm_erdos_ap_conjecture
-- name    : erdos_ap_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T01:49:22.186904+00:00
-- url     : https://prove2.me/theorems/6aa3c94f-3d32-4627-b1e3-d6b74628440a
-- statement:
--   Erdős conjecture on arithmetic progressions: Any set A ⊆ ℕ with ∑_{n∈A} 1/n = ∞ contains arbitrarily long arithmetic progressions. Green–Tao proved it for primes; the general case remains open.
-- source:
--   https://en.wikipedia.org/wiki/Erd%C5%91s_conjecture_on_arithmetic_progressions

import Mathlib

import Mathlib

theorem erdos_ap_conjecture :
    ∀ (A : Set ℕ),
      (∑' n : {n : ℕ // n ∈ A ∧ 1 ≤ n}, (1 : ENNReal) / n) = ⊤ →
      ∀ k : ℕ, ∃ a d : ℕ, 1 ≤ d ∧
        ∀ j : Fin k, a + j.val * d ∈ A := by
  sorry
