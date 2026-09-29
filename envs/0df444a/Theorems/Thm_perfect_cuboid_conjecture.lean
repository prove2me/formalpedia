-- Prove2me | Theorems.Thm_perfect_cuboid_conjecture
-- name    : perfect_cuboid_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T18:58:16.695958+00:00
-- url     : https://prove2.me/theorems/ea3e5ea0-37d8-4b4b-ab1a-be88734967a4
-- statement:
--   **Euler Brick / Perfect Cuboid Conjecture**: There is no "perfect cuboid" — a rectangular box with integer edge lengths $a, b, c$ such that all four space diagonals (face diagonals $\sqrt{a^2+b^2}$, $\sqrt{a^2+c^2}$, $\sqrt{b^2+c^2}$, and the space diagonal $\sqrt{a^2+b^2+c^2}$) are also integers.
--
--   An Euler brick (three face diagonals all integer) exists: e.g., $(240, 117, 44)$. Whether any Euler brick also has an integer space diagonal is unknown. Checked for $a \leq 10^{11}$ with no solution found.
--
--   **Source**: Guy, R.K. (2004). Unsolved Problems in Number Theory, 3rd ed., Springer, D18.
-- source:
--   https://en.wikipedia.org/wiki/Euler_brick#Perfect_cuboid

import Mathlib

theorem perfect_cuboid_conjecture :
    ¬∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
      ∃ d e f g : ℕ,
        a ^ 2 + b ^ 2 = d ^ 2 ∧
        a ^ 2 + c ^ 2 = e ^ 2 ∧
        b ^ 2 + c ^ 2 = f ^ 2 ∧
        a ^ 2 + b ^ 2 + c ^ 2 = g ^ 2 := by
  sorry
