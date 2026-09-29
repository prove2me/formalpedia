-- Prove2me | solution 1 for lean_workbook_plus_67381
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:50:45.512484+00:00
-- url     : https://prove2.me/submissions/ea6ebd49-e6c1-4854-b964-e335438e2941

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (n : ℕ) : n * (n + 1) / 2 = 55 ↔ n = 10 := by
  constructor
  · intro h
    have h1 : 110 ≤ n*(n+1) := by omega
    have h2 : n*(n+1) < 112 := by omega
    have hn1 : n ≤ 10 := by nlinarith
    have hn2 : 10 ≤ n := by nlinarith
    omega
  · rintro rfl
    norm_num
