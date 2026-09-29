-- Prove2me | Theorems.Thm_intermediate_value
-- name    : intermediate_value
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T15:20:12.477227+00:00
-- url     : https://prove2.me/theorems/4f01fbba-0e2a-447c-8665-bbb0eacedd83
-- statement:
--   Intermediate value theorem: A continuous function on [a,b] takes every value between f(a) and f(b).
-- source:
--   https://en.wikipedia.org/wiki/Intermediate_value_theorem

import Mathlib

import Mathlib

theorem intermediate_value (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (y : ℝ) (hy : min (f a) (f b) ≤ y ∧ y ≤ max (f a) (f b)) :
    ∃ c ∈ Set.Icc a b, f c = y := by
  sorry
