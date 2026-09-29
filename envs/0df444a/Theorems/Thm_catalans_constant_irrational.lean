-- Prove2me | Theorems.Thm_catalans_constant_irrational
-- name    : catalans_constant_irrational
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T21:35:32.00999+00:00
-- url     : https://prove2.me/theorems/fc539720-14b6-48e5-a544-f8dc28624def
-- statement:
--   Catalan's constant G = 1 - 1/9 + 1/25 - 1/49 + ... = ∑ (-1)ⁿ/(2n+1)² ≈ 0.9159... irrationality: Is Catalan's constant irrational? Not known; not even known to be irrational. Widely believed to be transcendental.
-- source:
--   https://en.wikipedia.org/wiki/Catalan%27s_constant

import Mathlib

import Mathlib

theorem catalans_constant_irrational :
    Irrational (∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ)) := by
  sorry
