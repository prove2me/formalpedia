-- Prove2me | solution 1 for lean_workbook_plus_33417
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:48:12.264312+00:00
-- url     : https://prove2.me/submissions/83a01bfb-03e7-4e6f-b07a-8c6f0dd89010

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution {x y z : ℤ} : x ≡ y [ZMOD z] ↔ z ∣ (x - y) := by
  rw [Int.modEq_iff_dvd, dvd_sub_comm]
