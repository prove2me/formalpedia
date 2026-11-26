-- Prove2me | solution 1 for ReweightedNPMLE.exists_local_positive_weight_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:59:26.600797+00:00
-- url     : https://prove2.me/submissions/6f55e322-9b0e-4440-8c06-59d907c0c83f

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
import Theorems.Thm_ReweightedNPMLE_exists_uniform_positive_coordinate_bounds

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
theorem solution {n : ℕ}
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) :
    ∃ a : ℝ, 0 < a ∧ ∃ s : Set (Fin n → ℝ),
      s ∈ nhds w ∧ ∀ u ∈ s, ∀ i, a ≤ u i := by
  have hsingle : ({w} : Set (Fin n → ℝ)) ⊆ positiveVectors n := by
    intro v hv
    simpa using (mem_singleton_iff.mp hv ▸ hw)
  obtain ⟨b, B, hb, _, hbound⟩ :=
    exists_uniform_positive_coordinate_bounds isCompact_singleton hsingle
  have hbw : ∀ i, b ≤ w i := fun i ↦ (hbound w (mem_singleton w) i).1
  let s : Set (Fin n → ℝ) := {u | ∀ i, b / 2 < u i}
  refine ⟨b / 2, by positivity, s, ?_, ?_⟩
  · change ∀ᶠ u in nhds w, ∀ i, b / 2 < u i
    rw [Filter.eventually_all]
    intro i
    exact (continuous_apply i).continuousAt.tendsto
      (Ioi_mem_nhds (by linarith [hbw i]))
  · intro u hu i
    exact (hu i).le
