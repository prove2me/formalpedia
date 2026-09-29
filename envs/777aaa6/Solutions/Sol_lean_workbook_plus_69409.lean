-- Prove2me | solution 1 for lean_workbook_plus_69409
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:24:24.626588+00:00
-- url     : https://prove2.me/submissions/ccc0198e-7926-40d5-bc66-cb3321a58e3c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c : ℝ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) (habc : a * b * c = 1) (h : (a - 1) * (b - 1) * (c - 1) = 6 * Real.sqrt 3 - 10) : a + b + c ≤ a * b * c := by
  clear habc
  let x := a - 1
  let y := b - 1
  let z := c - 1
  let r := Real.sqrt 3 - 1
  have hx : 0 < x := by dsimp [x]; linarith
  have hy : 0 < y := by dsimp [y]; linarith
  have hz : 0 < z := by dsimp [z]; linarith
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs3 := congrArg (fun t : ℝ => t * Real.sqrt 3) hs
  have hr : 0 < r := by dsimp [r]; nlinarith [Real.sqrt_nonneg 3]
  have hr2 : r ^ 2 = 4 - 2 * Real.sqrt 3 := by dsimp [r]; nlinarith
  have hxyz : x * y * z = r ^ 3 := by dsimp [x, y, z, r]; nlinarith
  let A := x * y / r ^ 2
  let B := y * z / r ^ 2
  let C := z * x / r ^ 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hp : A * B * C = 1 := by
    dsimp [A, B, C]
    field_simp [ne_of_gt hr]
    nlinarith [congrArg (fun t : ℝ => t ^ 2) hxyz]
  have hl := congrArg Real.log hp
  rw [Real.log_mul (by positivity) (ne_of_gt hC),
    Real.log_mul (ne_of_gt hA) (ne_of_gt hB), Real.log_one] at hl
  have hm : 3 ≤ A + B + C := by
    linarith [Real.log_le_sub_one_of_pos hA,
      Real.log_le_sub_one_of_pos hB, Real.log_le_sub_one_of_pos hC]
  have hm' : 3 ≤ (x * y + y * z + z * x) / r ^ 2 := by
    simpa only [A, B, C, add_div] using hm
  have hpair := (le_div_iff₀ (by positivity : 0 < r ^ 2)).mp hm'
  have hval : x * y * z = 6 * Real.sqrt 3 - 10 := h
  have hf : a * b * c - (a + b + c) =
      x * y * z + (x * y + y * z + z * x) - 2 := by
    dsimp [x, y, z]; ring
  nlinarith
