-- Prove2me | Theorems.Thm_pigeonhole_principle
-- name    : pigeonhole_principle
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T15:19:59.600743+00:00
-- url     : https://prove2.me/theorems/0ac1516a-d677-4e57-ab93-10e4e87da568
-- statement:
--   Pigeonhole principle: m objects into n < m boxes means some box has ≥ 2 objects.
-- source:
--   https://en.wikipedia.org/wiki/Pigeonhole_principle

import Mathlib

import Mathlib

theorem pigeonhole_principle (m n : ℕ) (hmn : n < m) (f : Fin m → Fin n) :
    ∃ i j : Fin m, i ≠ j ∧ f i = f j := by
  sorry
