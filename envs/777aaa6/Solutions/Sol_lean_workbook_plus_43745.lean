-- Prove2me | solution 1 for lean_workbook_plus_43745
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:24:10.191705+00:00
-- url     : https://prove2.me/submissions/08426443-dce4-41f8-ad24-1c71bd4cbf29

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ¬ Function.Injective (fun x : ℝ => 9*x - x^3) := by
  intro h
  have he : (9*(0:ℝ)-0^3) = 9*3-3^3 := by norm_num
  have := h he
  norm_num at this
