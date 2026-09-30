-- Prove2me | solution 1 for lean_workbook_plus_24900
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:19:15.361294+00:00
-- url     : https://prove2.me/submissions/16e2ceee-e685-4967-a98a-e1cbd27e5367

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

lemma square_parameter_identity (x y z A B C : ℝ)
    (hA : A ^ 2 = y + z) (hB : B ^ 2 = x + z) (hC : C ^ 2 = x + y) :
    (A + B + C) * (x * A + y * B + z * C - A * B * C) =
      2 * (x * y + y * z + z * x) := by
  have hx : x = (B ^ 2 + C ^ 2 - A ^ 2) / 2 := by linarith
  have hy : y = (A ^ 2 + C ^ 2 - B ^ 2) / 2 := by linarith
  have hz : z = (A ^ 2 + B ^ 2 - C ^ 2) / 2 := by linarith
  rw [hx, hy, hz]
  ring

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x * Real.sqrt (y + z) + y * Real.sqrt (x + z) + z * Real.sqrt (x + y) =
    Real.sqrt ((x + y) * (y + z) * (z + x)) +
      (2 * (x * y + y * z + z * x)) /
        (Real.sqrt (x + y) + Real.sqrt (y + z) + Real.sqrt (x + z)) := by
  have hxy : 0 ≤ x + y := le_of_lt (add_pos hx hy)
  have hyz : 0 ≤ y + z := le_of_lt (add_pos hy hz)
  have hxz : 0 ≤ x + z := le_of_lt (add_pos hx hz)
  have hprod : Real.sqrt ((x + y) * (y + z) * (z + x)) =
      Real.sqrt (x + y) * Real.sqrt (y + z) * Real.sqrt (x + z) := by
    rw [Real.sqrt_mul (mul_nonneg hxy hyz), Real.sqrt_mul hxy, add_comm z x]
  have hden : 0 < Real.sqrt (x + y) + Real.sqrt (y + z) + Real.sqrt (x + z) := by
    positivity
  have hid := square_parameter_identity x y z
    (Real.sqrt (y + z)) (Real.sqrt (x + z)) (Real.sqrt (x + y))
    (Real.sq_sqrt hyz) (Real.sq_sqrt hxz) (Real.sq_sqrt hxy)
  rw [hprod]
  field_simp [ne_of_gt hden]
  linear_combination hid
