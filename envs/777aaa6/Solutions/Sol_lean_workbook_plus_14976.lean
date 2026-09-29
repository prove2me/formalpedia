-- Prove2me | solution 1 for lean_workbook_plus_14976
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:57:24.830636+00:00
-- url     : https://prove2.me/submissions/3e8b7cc1-a35f-46b2-8599-13454a8644b1

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ¬ ∃ (x y z : ℝ), (x + y + z = 20 ∧ x*y + y*z + x*z = 150) := by
  rintro ⟨x, y, z, h₁, h₂⟩
  nlinarith [sq_nonneg (x-y), sq_nonneg (y-z), sq_nonneg (z-x)]
