-- Prove2me | solution 1 for BookSixth.planar_euler_counting_shell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T23:42:05.110719+00:00
-- url     : https://prove2.me/submissions/b585306c-cef8-4bfa-b360-52992d34af6f

import Mathlib
open scoped BigOperators

theorem solution (nV nE nF : ℕ) (hV : 3 ≤ nV) (hEuler : nV + nF = nE + 2) (hinc : 3 * nF ≤ 2 * nE) : nE ≤ 3 * nV - 6 := by
  omega
