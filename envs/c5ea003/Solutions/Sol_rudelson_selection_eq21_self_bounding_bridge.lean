-- Prove2me | solution 1 for rudelson_selection_eq21_self_bounding_bridge
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-06-23T23:41:38.822982+00:00
-- url     : https://prove2.me/submissions/57081a5c-3eb7-4bb3-8837-1ac35b0f88fc

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

set_option maxHeartbeats 1000000

/-
Rudelson 1999 (J. Funct. Anal. 164), proof of Theorem 1, eq (2.1) self-bounding step.
Abstract real-analysis bridge:  if `0 ≤ D` and `D ≤ A * √(D+1)` with `0 ≤ A`,
then `D ≤ A + A * √D`.
Key inequality: `√(D+1) ≤ 1 + √D` (since `D+1 ≤ (1+√D)² = 1 + 2√D + D`).
This is exactly the `D ≤ A(D+1)^{1/2} ≤ A + A√D` step in Rudelson p.4.
-/

theorem solution (D A : ℝ) (hD : 0 ≤ D) (hA : 0 ≤ A)
    (hrec : D ≤ A * Real.sqrt (D + 1)) :
    D ≤ A + A * Real.sqrt D := by
  -- √(D+1) ≤ 1 + √D
  have hsqrtD : 0 ≤ Real.sqrt D := Real.sqrt_nonneg D
  have hkey : Real.sqrt (D + 1) ≤ 1 + Real.sqrt D := by
    rw [show (1 : ℝ) + Real.sqrt D = Real.sqrt D + 1 by ring]
    -- compare squares; both sides nonneg
    have h1 : (0:ℝ) ≤ Real.sqrt D + 1 := by positivity
    rw [← Real.sqrt_sq h1]
    apply Real.sqrt_le_sqrt
    have hsq : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD
    nlinarith [Real.sqrt_nonneg D, hsq]
  -- A * √(D+1) ≤ A * (1 + √D) = A + A√D
  have hstep : A * Real.sqrt (D + 1) ≤ A * (1 + Real.sqrt D) :=
    mul_le_mul_of_nonneg_left hkey hA
  have : A * (1 + Real.sqrt D) = A + A * Real.sqrt D := by ring
  linarith [hrec, hstep, this.le, this.ge]

