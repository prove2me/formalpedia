-- Prove2me | solution 1 for lean_workbook_plus_62898
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:53:42.778832+00:00
-- url     : https://prove2.me/submissions/657054d2-2bcc-490f-a54d-0654464996d8

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (x y z : ℝ) (h : 0 < x ∧ 0 < y ∧ 0 < z) :
  x * (1/y + 1/z) ≥ 4*x/(y+z) := by
  rcases h with ⟨hx,hy,hz⟩
  have hi : x*(1/y+1/z)-4*x/(y+z) = x*(y-z)^2/(y*z*(y+z)) := by
    field_simp
    ring
  have hn : 0 ≤ x*(y-z)^2/(y*z*(y+z)) := by positivity
  linarith
