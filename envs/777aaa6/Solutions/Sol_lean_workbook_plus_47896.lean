-- Prove2me | solution 1 for lean_workbook_plus_47896
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:46:29.329708+00:00
-- url     : https://prove2.me/submissions/eac1dd73-560e-476d-a376-dbab18103e28

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + 2 / a - 5 * b / 4 + 4 / b = 5) : a + b ≥ 2 := by
  have heA : (2/a+9*a/2-6)*(2*a)=(3*a-2)^2 := by
    field_simp
    <;> ring
  have heB : (4/b+9*b/4-6)*(4*b)=(3*b-4)^2 := by
    field_simp
    <;> ring
  have hA : 0 ≤ 2/a+9*a/2-6 :=
    (mul_nonneg_iff_of_pos_right (show 0 < 2*a by positivity)).mp (by rw [heA]; exact sq_nonneg _)
  have hB : 0 ≤ 4/b+9*b/4-6 :=
    (mul_nonneg_iff_of_pos_right (show 0 < 4*b by positivity)).mp (by rw [heB]; exact sq_nonneg _)
  linarith only [hab, hA, hB]
