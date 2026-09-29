-- Prove2me | solution 1 for lean_workbook_plus_8987
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:05:06.056352+00:00
-- url     : https://prove2.me/submissions/9c2cf836-1fd4-44ef-9b5a-e4411081666b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y z : ℝ) (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1) (hz : 0 < z ∧ z < 1) : x * (1 - y) + y * (1 - z) + z * (1 - x) < 1 := by
  have h1 := mul_pos (mul_pos hx.1 hy.1) hz.1
  have h2 := mul_pos (mul_pos (show 0 < 1-x by linarith [hx.2]) (show 0 < 1-y by linarith [hy.2])) (show 0 < 1-z by linarith [hz.2])
  nlinarith
