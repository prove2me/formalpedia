-- Prove2me | solution 1 for lean_workbook_plus_59724
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:51:32.312717+00:00
-- url     : https://prove2.me/submissions/f0bb8ed7-6ed1-4520-b461-62117d1ac86d

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (n : ℕ) : (n * (n + 1)) / 2 = ((2 * n + 1)^2 - 1) / 8 := by
  have he : (2*n+1)^2 = 4*(n*(n+1))+1 := by ring
  have h : (2*n+1)^2-1 = 4*(n*(n+1)) := by omega
  rw [h]
  omega
