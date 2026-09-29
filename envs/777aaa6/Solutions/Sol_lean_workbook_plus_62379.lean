-- Prove2me | solution 1 for lean_workbook_plus_62379
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:56:55.201099+00:00
-- url     : https://prove2.me/submissions/39a72ffe-5f28-4992-8585-9df08d5ca6b0

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (x y z : ℝ) (h : x ∈ Set.Ioo 0 1 ∧ y ∈ Set.Ioo 0 1 ∧ z ∈ Set.Ioo 0 1 ∧ x * y + y * z + z * x = 1) :
  x + y + z ≤ 2 := by
  rcases h with ⟨hx,hy,hz,he⟩
  have hp := mul_pos (mul_pos (show 0 < 1-x by linarith [hx.2]) (show 0 < 1-y by linarith [hy.2])) (show 0 < 1-z by linarith [hz.2])
  have hxyz := mul_pos (mul_pos hx.1 hy.1) hz.1
  nlinarith
