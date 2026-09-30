-- Prove2me | solution 1 for lean_workbook_plus_21
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:24:54.60684+00:00
-- url     : https://prove2.me/submissions/058cf28a-8754-45dd-9ade-f90b31a004e6

import Mathlib

theorem solution (n p q : ℕ) (hp : p ≤ n) (hq : q ≤ p) :
    (n - q).choose (p - q) * n.choose q = n.choose p * p.choose q := by
  simpa only [mul_comm] using (Nat.choose_mul (n := n) hq).symm
