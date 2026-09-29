-- Prove2me | solution 1 for lean_workbook_plus_10999
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T03:12:50.281584+00:00
-- url     : https://prove2.me/submissions/a4c044ac-4b08-4d90-96a5-db833deb2ba0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

private theorem square_le_cube (n : ℕ) : n ^ 2 ≤ n ^ 3 := by
  by_cases hn : n = 0
  · simp [hn]
  have h1 : 1 ≤ n := by omega
  have h2 := Nat.mul_le_mul_left (n ^ 2) h1
  nlinarith

private theorem full_source (a b c : ℕ) :
    5 * (a ^ 2 + b ^ 2 + c ^ 2) ≤ 6 * (a ^ 3 + b ^ 3 + c ^ 3) + 1 := by
  nlinarith [square_le_cube a, square_le_cube b, square_le_cube c]

theorem solution (a b c : ℕ) (hab : a + b + c = 1) :
    5 * (a ^ 2 + b ^ 2 + c ^ 2) ≤ 6 * (a ^ 3 + b ^ 3 + c ^ 3) + 1 := by
  exact full_source a b c
