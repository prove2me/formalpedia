-- Prove2me | solution 1 for ReweightedNPMLE.sqrt_sub_sq_le_abs_sub
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:04:04.606783+00:00
-- url     : https://prove2.me/submissions/7ded26ca-d66d-43e8-bec4-3ecf81258e6b

import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_Hellinger

/-!
# Squared Hellinger distance

This file formalizes the normalization convention used in the manuscript,
`H²(p,q) = ∫ (√p-√q)²`, and its affinity identity.
-/

open MeasureTheory Filter Topology

open ReweightedNPMLE
open ReweightedNPMLE in
/-- The pointwise squared Hellinger integrand is bounded by absolute
density error. -/
theorem solution {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ |a - b| := by
  have hsqrt : |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt a + Real.sqrt b := by
    calc
      |Real.sqrt a - Real.sqrt b| ≤ |Real.sqrt a| + |Real.sqrt b| := abs_sub _ _
      _ = Real.sqrt a + Real.sqrt b := by
        rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    (Real.sqrt a - Real.sqrt b) ^ 2 =
        |Real.sqrt a - Real.sqrt b| ^ 2 := (sq_abs _).symm
    _ ≤ |Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b) :=
      by simpa [pow_two] using
        mul_le_mul_of_nonneg_left hsqrt (abs_nonneg (Real.sqrt a - Real.sqrt b))
    _ = |a - b| := by
      rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),
        ← abs_mul]
      apply congrArg abs
      calc
        (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) =
            Real.sqrt a ^ 2 - Real.sqrt b ^ 2 := by ring
        _ = a - b := by rw [Real.sq_sqrt ha, Real.sq_sqrt hb]
