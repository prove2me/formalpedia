-- Prove2me | solution 2 for lean_workbook_plus_57196
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:17:39.646397+00:00
-- url     : https://prove2.me/submissions/6bd38d56-0b4d-4854-be7c-449a3fef88ac

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z r s : ℂ) : (x = r * (r + s) ∧ y = r * s ∧ z = s * (r + s)) → x * y + z * y = x * z := by
  rintro ⟨rfl,rfl,rfl⟩
  ring
