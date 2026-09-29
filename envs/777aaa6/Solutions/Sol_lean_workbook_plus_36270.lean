-- Prove2me | solution 1 for lean_workbook_plus_36270
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:50:54.396783+00:00
-- url     : https://prove2.me/submissions/a5b0bf92-41b7-40d9-8e46-c5448cc1c679

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution {a n : ℕ} (h : Nat.gcd a n = 1) : ∃ x y : ℤ, a * x + n * y = 1 := by
  refine ⟨Nat.gcdA a n, Nat.gcdB a n, ?_⟩
  have hh := Nat.gcd_eq_gcd_ab a n
  rw [h] at hh
  simpa using hh.symm
