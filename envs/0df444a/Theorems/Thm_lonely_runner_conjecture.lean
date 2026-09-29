-- Prove2me | Theorems.Thm_lonely_runner_conjecture
-- name    : lonely_runner_conjecture
-- status  : Disproved
-- author  : @tianyipeng
-- created : 2026-05-31T20:36:26.617743+00:00
-- url     : https://prove2.me/theorems/87206da5-d84c-4048-b568-15cbfd12ae3f
-- statement:
--   The lonely runner conjecture (Wills 1967, Cusick 1973): If n runners with distinct constant speeds run around a unit-length circular track, then for each runner there is a time when they are at distance ≥ 1/(n+1) from all others. Proved for n ≤ 7 (Barajas–Serra 2008). Open for n ≥ 8.
-- source:
--   https://en.wikipedia.org/wiki/Lonely_runner_conjecture

import Mathlib

import Mathlib

theorem lonely_runner_conjecture (n : ℕ) (hn : 1 ≤ n)
    (speeds : Fin n → ℝ)
    (hdist : ∀ i j : Fin n, i ≠ j → speeds i ≠ speeds j) :
    ∃ t : ℝ, 0 < t ∧
      ∀ i : Fin n,
        let pos := Int.fract (speeds i * t)
        (1 : ℝ) / (n + 1) ≤ pos ∧ pos ≤ 1 - 1 / (n + 1) := by
  sorry
