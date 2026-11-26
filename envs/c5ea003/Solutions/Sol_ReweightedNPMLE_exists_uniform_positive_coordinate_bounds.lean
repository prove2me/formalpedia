-- Prove2me | solution 1 for ReweightedNPMLE.exists_uniform_positive_coordinate_bounds
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:53:15.852071+00:00
-- url     : https://prove2.me/submissions/7a3f364c-8760-4d3b-a9fc-8de9cf3e2245

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Regularity of the fitted-value problem

This file proves the analytic regularity part of the paper's effective-dimension
argument.  Variational inequalities yield a quantitative local Lipschitz bound
for the unique fitted vector and its coordinatewise logarithm.  Mathlib's
Rademacher theorem then gives almost-everywhere differentiability.
-/

open Set MeasureTheory Filter
open scoped BigOperators NNReal

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Compactness inside the positive orthant gives common positive lower
and upper bounds for every feasible coordinate. -/
theorem solution {n : ℕ}
    {C : Set (Fin n → ℝ)} (hCcompact : IsCompact C)
    (hCpos : C ⊆ positiveVectors n) :
    ∃ c B : ℝ, 0 < c ∧ 0 < B ∧ ∀ v ∈ C, ∀ i, c ≤ v i ∧ v i ≤ B := by
  let z : (Fin n → ℝ) → (Fin n → ℝ) := fun v i ↦ Real.log (v i)
  have hz : ContinuousOn z C := by
    apply continuousOn_pi.mpr
    intro i
    exact (continuous_apply i).continuousOn.log (fun v hv ↦ (hCpos hv i).ne')
  obtain ⟨M, hMpos, hM⟩ := (hCcompact.image_of_continuousOn hz).isBounded.exists_pos_norm_le
  refine ⟨Real.exp (-M), Real.exp M, Real.exp_pos _, Real.exp_pos _, ?_⟩
  intro v hv i
  have hi : |Real.log (v i)| ≤ M := by
    exact (norm_le_pi_norm (z v) i).trans (hM (z v) ⟨v, hv, rfl⟩)
  rw [abs_le] at hi
  constructor
  · rw [← Real.exp_log (hCpos hv i)]
    exact Real.exp_le_exp.mpr hi.1
  · rw [← Real.exp_log (hCpos hv i)]
    exact Real.exp_le_exp.mpr hi.2
