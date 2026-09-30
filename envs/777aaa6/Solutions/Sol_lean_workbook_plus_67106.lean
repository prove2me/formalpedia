-- Prove2me | solution 1 for lean_workbook_plus_67106
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:10:40.943206+00:00
-- url     : https://prove2.me/submissions/af5d7f9d-e94d-4a2d-a85b-1ac521cae35d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (x y z : ℝ) (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1)
    (hz : 0 < z ∧ z < 1) (h : x * y + y * z + z * x = 1) :
    1 ≤ x + y + z + x * y * z ∧ x + y + z + x * y * z ≤ 2 := by
  have hxy : 0 ≤ x * (1 - y) := mul_nonneg hx.1.le (by linarith [hy.2])
  have hyz : 0 ≤ y * (1 - z) := mul_nonneg hy.1.le (by linarith [hz.2])
  have hzx : 0 ≤ z * (1 - x) := mul_nonneg hz.1.le (by linarith [hx.2])
  have hp : 0 ≤ x * y * z := mul_nonneg (mul_nonneg hx.1.le hy.1.le) hz.1.le
  have hc : 0 ≤ (1 - x) * (1 - y) * (1 - z) :=
    mul_nonneg (mul_nonneg (by linarith [hx.2]) (by linarith [hy.2]))
      (by linarith [hz.2])
  constructor <;> nlinarith

#print axioms solution
