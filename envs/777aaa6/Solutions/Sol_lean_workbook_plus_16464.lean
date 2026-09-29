-- Prove2me | solution 1 for lean_workbook_plus_16464
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:05:12.410139+00:00
-- url     : https://prove2.me/submissions/a263821a-3424-4fab-a56e-75d00b947cd7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b d : ℤ) (hd : d = gcd a b) : ∃ x y : ℤ, d = a * x + b * y := by
  change d=(Int.gcd a b : ℤ) at hd
  refine ⟨Int.gcdA a b,Int.gcdB a b,?_⟩
  rw [hd]
  exact Int.gcd_eq_gcd_ab a b
