-- Prove2me | solution 1 for cyclotomic5_mod5
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T08:04:47.185455+00:00
-- url     : https://prove2.me/submissions/54130049-1cd3-4c12-8ca4-076a09b799e6

import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

theorem solution : ¬ (∀ a b : ℤ, (5 : ℤ) ∣ (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) - (a - b) ^ 4) := by
  intro h
  have h11 := h 1 1
  norm_num at h11
  omega
