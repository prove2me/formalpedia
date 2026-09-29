-- Prove2me | solution 1 for lean_workbook_plus_36423
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:56:02.732294+00:00
-- url     : https://prove2.me/submissions/44bde341-785b-4db4-b0c8-bd4a65af026a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (n : ℕ) : n^2225 - n^2005 = n^2005 * (n^220 - 1) := by
  calc
    n^2225-n^2005 = n^2005*n^220-n^2005 := by rw [← pow_add]
    _ = n^2005*(n^220-1) := by rw [Nat.mul_sub_left_distrib,mul_one]
