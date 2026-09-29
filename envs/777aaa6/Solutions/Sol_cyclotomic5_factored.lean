-- Prove2me | solution 1 for cyclotomic5_factored
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T07:06:20.830216+00:00
-- url     : https://prove2.me/submissions/df53ba2f-710f-4a45-bd29-58fef813c5cc

import Theorems.Thm_cyclotomic5_factored
import Mathlib.Tactic.Ring

theorem solution (a b : ℤ) :
    (a + b) * (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) = a ^ 5 + b ^ 5 := by ring
