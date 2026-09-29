-- Prove2me | solution 1 for lean_workbook_plus_40055
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:15:31.100148+00:00
-- url     : https://prove2.me/submissions/ac42e103-0c24-420c-94fe-62d7d276a9f8

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution {x y : ℝ} (hx : x > 0) (hy : y > 0) (hxy : x + y = 1) : 6 + 27 - (18 * (x + 2 * y)) / (2 * x + y) ≤ 15 * x / y ↔ (x - y) * (10 * x - y) ≥ 0 := by
  clear hxy
  have hp : 0 < 2*x+y := by linarith
  have hd : 0 < y*(2*x+y) := mul_pos hy hp
  have he : 15*x/y-(6+27-18*(x+2*y)/(2*x+y)) = 3*((x-y)*(10*x-y))/(y*(2*x+y)) := by
    field_simp [ne_of_gt hy, ne_of_gt hp]
    <;> ring
  constructor
  · intro h
    have hq : 0 ≤ 3*((x-y)*(10*x-y))/(y*(2*x+y)) := by linarith
    rcases div_nonneg_iff.mp hq with hn | hn
    · linarith [hn.1]
    · linarith [hn.2]
  · intro h
    have hq : 0 ≤ 3*((x-y)*(10*x-y))/(y*(2*x+y)) := div_nonneg (by linarith) hd.le
    linarith
