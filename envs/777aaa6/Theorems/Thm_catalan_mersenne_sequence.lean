-- Prove2me | Theorems.Thm_catalan_mersenne_sequence
-- name    : catalan_mersenne_sequence
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T02:36:11.871023+00:00
-- url     : https://prove2.me/theorems/3bed46d3-09fa-4276-abc8-f9031bf95030
-- statement:
--   Catalan-Mersenne conjecture: All terms in the sequence M₀=2, M₁=3, M₂=7, M₃=127, M₄=2^127-1,... are prime, where Mₙ₊₁=2^{Mₙ}-1. M₄ is prime (verified); M₅=2^{M₄}-1 is far too large to verify. Almost certainly true for the first few but proving it for any M₅ is beyond current technology.
-- source:
--   https://en.wikipedia.org/wiki/Double_Mersenne_number

import Mathlib

import Mathlib

def catMersenne : ℕ → ℕ
    | 0 => 2
    | n + 1 => 2 ^ catMersenne n - 1

theorem catalan_mersenne_sequence :
    ∀ n : ℕ, Nat.Prime (catMersenne n) := by
  sorry
