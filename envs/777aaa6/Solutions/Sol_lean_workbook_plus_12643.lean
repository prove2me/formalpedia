-- Prove2me | solution 1 for lean_workbook_plus_12643
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:00:35.847457+00:00
-- url     : https://prove2.me/submissions/3524b292-b197-460c-aaae-38bc66f46907

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000


theorem solution (m n : ℤ) : ∃ m n, (m+1)*(n-1) = (m-n+1)*(m-n-1) := by
  refine ⟨1, 1, ?_⟩ <;> norm_num at *
