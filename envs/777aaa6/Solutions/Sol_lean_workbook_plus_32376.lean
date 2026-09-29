-- Prove2me | solution 1 for lean_workbook_plus_32376
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:22:18.972375+00:00
-- url     : https://prove2.me/submissions/8e16af03-1232-49e2-9df8-7b753307178d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℤ) (n : ℕ) (hx: x ≠ 1) : x - 1 ∣ x ^ n - 1 := by
  intros
  exact sub_one_dvd_pow_sub_one x n
