-- Prove2me | solution 1 for lean_workbook_plus_19718
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:28:37.79515+00:00
-- url     : https://prove2.me/submissions/38d9b4c5-67b4-4c23-adeb-5fb6b3552ee0

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (n : ℕ) : (1 : ℚ) / (n + 1) = 2 / (2 * n + 2) := by
  field_simp
  <;> ring
