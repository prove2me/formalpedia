-- Prove2me | solution 1 for cyclotomic_phi5_congruence
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T05:41:09.565803+00:00
-- url     : https://prove2.me/submissions/c4e48465-48ac-47b1-aa42-920f4563bc05

import Theorems.Thm_cyclotomic_phi5_congruence
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

theorem solution (a b : ℤ) : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 - 5 * b ^ 4 = (a + b) * (a ^ 3 - 2 * a ^ 2 * b + 3 * a * b ^ 2 - 4 * b ^ 3) := by
  ring
