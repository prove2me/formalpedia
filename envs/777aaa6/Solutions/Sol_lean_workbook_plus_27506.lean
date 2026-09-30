-- Prove2me | solution 1 for lean_workbook_plus_27506
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:54:09.741663+00:00
-- url     : https://prove2.me/submissions/125dcedb-eeea-40f5-8ba9-abce92a9afee

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem coordinate_bound (x y z : Real) (hs : x + y + z = 6)
    (hp : x * y + y * z + z * x = 9) : 0 ≤ x ∧ x ≤ 4 := by
  have hz : z = 6 - x - y := by linarith
  rw [hz] at hp
  have hq : x ^ 2 ≤ 4 * x := by
    nlinarith [sq_nonneg (x + 2 * y - 6)]
  constructor
  · nlinarith [sq_nonneg x]
  · nlinarith [sq_nonneg (x - 4)]

theorem solution (x y z : Real) (hx : x + y + z = 6)
    (hy : x * y + y * z + z * x = 9) :
    0 ≤ x ∧ x ≤ 4 ∧ 0 ≤ y ∧ y ≤ 4 ∧ 0 ≤ z ∧ z ≤ 4 := by
  have hxb := coordinate_bound x y z hx hy
  have hyb := coordinate_bound y z x (by linarith) (by nlinarith)
  have hzb := coordinate_bound z x y (by linarith) (by nlinarith)
  exact ⟨hxb.1, hxb.2, hyb.1, hyb.2, hzb.1, hzb.2⟩

#print axioms solution
