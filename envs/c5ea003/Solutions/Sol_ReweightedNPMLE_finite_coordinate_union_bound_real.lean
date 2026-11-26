-- Prove2me | solution 1 for ReweightedNPMLE.finite_coordinate_union_bound_real
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:08:56.830687+00:00
-- url     : https://prove2.me/submissions/c3dbd6a1-78b3-4a4e-9a5c-af8a32afdf4e

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Tactic

/-!
# Gamma moment generating function and coordinate tails

The paper uses shape--rate Gamma variables.  This file connects the scalar
logarithm inequalities in `GammaBounds` to mathlib's actual
`ProbabilityTheory.gammaMeasure`.
-/

open MeasureTheory Real Set
open ProbabilityTheory
/-- A finite family of coordinate tail bounds gives a maximum-coordinate
bound, with no independence assumption needed for this union-bound step. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (W : Fin n → Ω → ℝ) {t b : ℝ}
    (hcoord : ∀ i, μ.real {ω | |W i ω - 1| > t} ≤ b) :
    μ.real {ω | ∃ i, |W i ω - 1| > t} ≤ n * b := by
  have hset : {ω | ∃ i, |W i ω - 1| > t} =
      ⋃ i : Fin n, {ω | |W i ω - 1| > t} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  rw [hset]
  calc
    μ.real (⋃ i : Fin n, {ω | |W i ω - 1| > t}) ≤
        ∑ i : Fin n, μ.real {ω | |W i ω - 1| > t} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : Fin n, b := Finset.sum_le_sum fun i _ ↦ hcoord i
    _ = n * b := by simp
