-- Prove2me | solution 1 for lean_workbook_plus_16961
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:00:21.850116+00:00
-- url     : https://prove2.me/submissions/4bb79c84-5648-469a-ab7c-7145de655a90

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (n : ℕ) (_h : 2 ≤ n) : n ≤ 2 ^ (n - 1) := by
  have hh : n-1 < 2^(n-1) := Nat.lt_two_pow_self
  omega
