-- Prove2me | solution 1 for lean_workbook_plus_34977
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:01:51.93951+00:00
-- url     : https://prove2.me/submissions/9057c40c-0bfc-4742-a2eb-bc18bae55582

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y : ℤ) (hxy: gcd x y = 1) : ∃ a b: ℤ, a*x + b*y = 1 := by
  change (Int.gcd x y : ℤ)=1 at hxy
  refine ⟨Int.gcdA x y,Int.gcdB x y,?_⟩
  have hh := Int.gcd_eq_gcd_ab x y
  rw [hxy] at hh
  simpa [mul_comm] using hh.symm
