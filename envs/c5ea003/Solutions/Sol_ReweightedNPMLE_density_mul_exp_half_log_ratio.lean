-- Prove2me | solution 1 for ReweightedNPMLE.density_mul_exp_half_log_ratio
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:05:00.904388+00:00
-- url     : https://prove2.me/submissions/faea690b-eb89-449a-9b47-135707a9b8d2

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

-- Inline helpers preserved from ReweightedNPMLE.Hellinger.
section
/-!
# Squared Hellinger distance

This file formalizes the normalization convention used in the manuscript,
`H²(p,q) = ∫ (√p-√q)²`, and its affinity identity.
-/

open MeasureTheory Filter Topology

namespace ReweightedNPMLE









































/-- Pointwise square-root likelihood-ratio identity. -/
theorem exp_half_log_ratio_eq_sqrt {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    Real.exp (Real.log (p / q) / 2) = Real.sqrt (p / q) := by
  have hpq : 0 < p / q := div_pos hp hq
  symm
  apply (Real.sqrt_eq_iff_mul_self_eq hpq.le (Real.exp_pos _).le).2
  rw [← Real.exp_add, ← two_mul, show 2 * (Real.log (p / q) / 2) =
      Real.log (p / q) by ring, Real.exp_log hpq]















end ReweightedNPMLE
end

/-!
# Squared Hellinger distance

This file formalizes the normalization convention used in the manuscript,
`H²(p,q) = ∫ (√p-√q)²`, and its affinity identity.
-/

open MeasureTheory Filter Topology

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Multiplying the square-root likelihood ratio by the reference density gives affinity. -/
theorem solution {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    q * Real.exp (Real.log (p / q) / 2) = Real.sqrt (p * q) := by
  rw [exp_half_log_ratio_eq_sqrt hp hq]
  symm
  apply (Real.sqrt_eq_iff_mul_self_eq (mul_pos hp hq).le
    (mul_nonneg hq.le (Real.sqrt_nonneg _))).2
  have hr2 : Real.sqrt (p / q) * Real.sqrt (p / q) = p / q := by
    rw [← pow_two, Real.sq_sqrt (div_pos hp hq).le]
  calc
    p * q = q * q * (p / q) := by field_simp [hq.ne']
    _ = q * q * (Real.sqrt (p / q) * Real.sqrt (p / q)) :=
      congrArg (fun z ↦ q * q * z) hr2.symm
    _ = (q * Real.sqrt (p / q)) * (q * Real.sqrt (p / q)) := by ring
