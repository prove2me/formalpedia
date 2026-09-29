-- Prove2me | Theorems.Thm_chromatic_number_plane_at_least_5
-- name    : chromatic_number_plane_at_least_5
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T20:58:20.60183+00:00
-- url     : https://prove2.me/theorems/d4752d99-bf7e-4a7e-9c8f-8e89e689f8b4
-- statement:
--   The chromatic number of the plane is at least 5 (de Grey 2018): No 4-coloring of the plane can avoid monochromatic unit distances. de Grey constructed a finite unit-distance graph with chromatic number 5, settling the lower bound from 4 to 5. The exact value (5, 6, or 7) remains open.
-- source:
--   https://en.wikipedia.org/wiki/Hadwiger%E2%80%93Nelson_problem

import Mathlib

import Mathlib

theorem chromatic_number_plane_at_least_5 :
    ∀ (col : ℝ × ℝ → Fin 4),
      ∃ p q : ℝ × ℝ, (p.1 - q.1)^2 + (p.2 - q.2)^2 = 1 ∧ col p = col q := by
  sorry
