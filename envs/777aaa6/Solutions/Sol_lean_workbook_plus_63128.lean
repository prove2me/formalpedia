-- Prove2me | solution 1 for lean_workbook_plus_63128
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:49:17.835807+00:00
-- url     : https://prove2.me/submissions/2a82ff88-3499-420f-aaf0-af612983bda6

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (m n x : ℝ) : (Int.floor (m * x) + Int.floor (n * x) : ℝ) ≤ Int.floor ((m + n) * x) := by
  have hi : Int.floor (m*x)+Int.floor (n*x) ≤ Int.floor ((m+n)*x) := by
    apply Int.le_floor.mpr
    push_cast
    rw [add_mul]
    exact add_le_add (Int.floor_le (m*x)) (Int.floor_le (n*x))
  exact_mod_cast hi
