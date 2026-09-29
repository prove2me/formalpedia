-- Prove2me | solution 1 for lean_workbook_plus_69086
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T22:46:09.305573+00:00
-- url     : https://prove2.me/submissions/d2981c8a-fc71-4fc6-8494-5061d5217d19

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b : ℕ} : Nat.lcm a b = a * b / Nat.gcd a b := by
  exact Nat.lcm_eq_mul_div a b
