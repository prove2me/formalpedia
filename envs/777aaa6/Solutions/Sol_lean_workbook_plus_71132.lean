-- Prove2me | solution 1 for lean_workbook_plus_71132
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:33:37.040476+00:00
-- url     : https://prove2.me/submissions/5d839eaf-25c5-42f3-b9e8-300648afcaca

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : dist (6, 0) (-2, 0) = 8 := by
  have hAxis (a b : ℤ) (c : ℕ) :
      dist (a,c) (b,c) = Real.sqrt (((a:ℝ)-b)^2 + ((c:ℝ)-c)^2) := by
    simp [Prod.dist_eq, Int.dist_eq, Real.sqrt_sq_eq_abs]
  have hEuclidean : Real.sqrt (((6:ℝ)-(-2))^2 + ((0:ℝ)-0)^2) = 8 := by
    rw [show (((6:ℝ)-(-2))^2 + ((0:ℝ)-0)^2) = (8:ℝ)^2 by ring]
    rw [Real.sqrt_sq_eq_abs]
    norm_num
  apply (hAxis 6 (-2) 0).trans
  simpa only [Int.cast_ofNat, Int.cast_neg, Nat.cast_ofNat, Nat.cast_zero] using hEuclidean
