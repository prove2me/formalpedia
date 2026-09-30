-- Prove2me | solution 1 for lean_workbook_plus_40206
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:17:50.771687+00:00
-- url     : https://prove2.me/submissions/570a819a-a451-4141-bff6-80dd6d641356

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℕ) : n ≤ 2 ^ (n - 1) := by
  rcases n with _ | m
  · simp
  · simpa using Nat.lt_two_pow_self (n := m)
