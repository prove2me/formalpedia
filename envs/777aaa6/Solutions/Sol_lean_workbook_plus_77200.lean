-- Prove2me | solution 1 for lean_workbook_plus_77200
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:08:47.082362+00:00
-- url     : https://prove2.me/submissions/9c5625ef-2359-44f3-90f1-0c8ee7d7d27a

import Mathlib.NumberTheory.Divisors

theorem solution : ∀ n : ℕ, n.divisors.card ≤ n :=
  Nat.card_divisors_le_self
