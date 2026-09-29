-- Prove2me | Theorems.Thm_cantor_uncountability
-- name    : cantor_uncountability
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T15:20:25.914015+00:00
-- url     : https://prove2.me/theorems/dde3e7bf-cd4a-4e6f-97dc-1631092e2d78
-- statement:
--   Cantor's theorem: The power set of any set is strictly larger. Specifically, ℕ is countable but its power set is not. Proved by Cantor (1891).
-- source:
--   https://en.wikipedia.org/wiki/Cantor%27s_theorem

import Mathlib

import Mathlib

theorem cantor_uncountability :
    ¬ ∃ f : ℕ → Set ℕ, Function.Surjective f := by
  sorry
