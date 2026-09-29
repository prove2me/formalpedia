-- Prove2me | Theorems.Thm_catalans_constant_transcendental
-- name    : catalans_constant_transcendental
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T03:27:48.631508+00:00
-- url     : https://prove2.me/theorems/964efe5d-3f33-4e79-b55e-c067df07e44f
-- statement:
--   Transcendence of Catalan's constant G ≈ 0.9159. Not even known to be irrational.
-- source:
--   https://en.wikipedia.org/wiki/Catalan%27s_constant

import Mathlib

import Mathlib

theorem catalans_constant_transcendental :
    Transcendental ℚ (∑' n : ℕ, (-1 : ℝ) ^ n / ((2 * n + 1) ^ 2 : ℝ)) := by
  sorry
