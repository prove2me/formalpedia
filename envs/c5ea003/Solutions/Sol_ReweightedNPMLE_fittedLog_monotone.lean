-- Prove2me | solution 1 for ReweightedNPMLE.fittedLog_monotone
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:01:46.761472+00:00
-- url     : https://prove2.me/submissions/78a00ab8-192f-46f2-a5dc-e82cff692e94

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
/-- The fitted log-vector is a monotone function of the likelihood weights. -/
theorem solution {n : ℕ} [Nonempty (Fin n)]
    {C : Set (Fin n → ℝ)}
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    {s : Set (Fin n → ℝ)}
    (hmax : ∀ w ∈ s, IsMaxOn C (weightedLogLikelihood w) (vhat w)) :
    ∀ w ∈ s, ∀ u ∈ s,
      0 ≤ ∑ i, (w i - u i) *
        (Real.log (vhat w i) - Real.log (vhat u i)) := by
  intro w hw u hu
  have hwu := (hmax w hw).2 (vhat u) (hmax u hu).1
  have huw := (hmax u hu).2 (vhat w) (hmax w hw).1
  unfold weightedLogLikelihood at hwu huw
  calc
    0 ≤ (∑ i, w i * Real.log (vhat w i)) -
        ∑ i, w i * Real.log (vhat u i) := sub_nonneg.mpr hwu
    _ ≤ ((∑ i, w i * Real.log (vhat w i)) -
        ∑ i, w i * Real.log (vhat u i)) +
        ((∑ i, u i * Real.log (vhat u i)) -
        ∑ i, u i * Real.log (vhat w i)) := by linarith
    _ = ∑ i, (w i - u i) *
        (Real.log (vhat w i) - Real.log (vhat u i)) := by
      simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
      ring
