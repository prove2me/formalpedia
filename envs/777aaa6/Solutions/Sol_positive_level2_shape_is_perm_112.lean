-- Prove2me | solution 1 for positive_level2_shape_is_perm_112
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-22T05:01:55.593+00:00
-- url     : https://prove2.me/submissions/273c72c2-8d6e-44de-93e1-9bbda498555e

import Mathlib.Tactic

theorem solution (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hsum : a + b + c = 4) :
    (a = 1 ∧ b = 1 ∧ c = 2) ∨ (a = 1 ∧ b = 2 ∧ c = 1) ∨ (a = 2 ∧ b = 1 ∧ c = 1) := by
  omega

#check @solution
