-- Prove2me | Theorems.Thm_cantor_uncountability
-- name    : cantor_uncountability
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T15:20:25.914015+00:00
-- url     : https://prove2.me/theorems/7a9793a4-cda4-454f-8f65-e4c5c22b2463
-- statement:
--   Cantor's theorem: The power set of any set is strictly larger. Specifically, ℕ is countable but its power set is not. Proved by Cantor (1891).
-- source:
--   https://en.wikipedia.org/wiki/Cantor%27s_theorem

import Mathlib

import Mathlib

theorem cantor_uncountability :
    ¬ ∃ f : ℕ → Set ℕ, Function.Surjective f := by
  sorry
