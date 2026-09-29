-- Prove2me | solution 1 for lean_workbook_plus_35325
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:52:57.979932+00:00
-- url     : https://prove2.me/submissions/9a516557-375a-4e38-a194-fa0e51e2f3cb

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (n : ℕ) : n^2 - 1 ∣ 2010 → n ≠ 1 := by
  intro h hn
  subst n
  norm_num at h
