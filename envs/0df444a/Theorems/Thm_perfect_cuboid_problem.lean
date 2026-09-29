-- Prove2me | Theorems.Thm_perfect_cuboid_problem
-- name    : perfect_cuboid_problem
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T20:44:17.226096+00:00
-- url     : https://prove2.me/theorems/552d9a1f-66f0-4433-bd03-7a989ae8817b
-- statement:
--   The perfect cuboid problem: Does there exist a rectangular box with integer dimensions where all face diagonals and the space diagonal are also integers? No perfect cuboid has been found despite extensive searches. The problem splits into cases: 'Euler brick' (all face diagonals integral) is possible, but adding the space diagonal is unresolved.
-- source:
--   https://en.wikipedia.org/wiki/Euler_brick

import Mathlib

import Mathlib

theorem perfect_cuboid_problem :
    ¬ ∃ (a b c : ℕ), 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧
      ∃ (dab dac dbc dabc : ℕ),
        a ^ 2 + b ^ 2 = dab ^ 2 ∧
        a ^ 2 + c ^ 2 = dac ^ 2 ∧
        b ^ 2 + c ^ 2 = dbc ^ 2 ∧
        a ^ 2 + b ^ 2 + c ^ 2 = dabc ^ 2 := by
  sorry
