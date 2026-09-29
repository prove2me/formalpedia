-- Prove2me | Theorems.Thm_euler_mascheroni_irrational
-- name    : euler_mascheroni_irrational
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T21:34:26.291171+00:00
-- url     : https://prove2.me/theorems/2fb79ee5-dcd4-4a82-ac25-74afad7d306d
-- statement:
--   Euler–Mascheroni constant γ ≈ 0.5772... irrationality: Is the Euler–Mascheroni constant γ = lim(1+1/2+...+1/n - ln n) irrational? γ is not known to be rational or irrational. Strong transcendence is suspected but totally unproved.
-- source:
--   https://en.wikipedia.org/wiki/Euler%E2%80%93Mascheroni_constant

import Mathlib

import Mathlib

theorem euler_mascheroni_irrational :
    Irrational (Real.exp (-Real.log 1) * ∫ x in Set.Ioi (0 : ℝ),
      Real.exp (-x) * Real.log x) := by
  sorry
