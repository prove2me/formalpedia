-- Prove2me | solution 1 for ReweightedNPMLE.fitted_maximizer_firstOrder_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:59:13.898223+00:00
-- url     : https://prove2.me/submissions/e1c03c76-32c0-497f-84d6-91bee25e3b46

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
import Theorems.Thm_ReweightedNPMLE_likelihoodContactNumerator_le_total_of_isMaxOn

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
/-- First-order variational inequality at a positive fitted-value maximizer. -/
theorem solution {n : ℕ} [Nonempty (Fin n)]
    {C : Set (Fin n → ℝ)} (hC : Convex ℝ C)
    (hCpos : C ⊆ positiveVectors n)
    (w v a : Fin n → ℝ) (hv : IsMaxOn C (weightedLogLikelihood w) v)
    (ha : a ∈ C) :
    ∑ i, w i * ((a i - v i) / v i) ≤ 0 := by
  have hraw := likelihoodContactNumerator_le_total_of_isMaxOn
    hC hCpos w v a hv ha
  have hvpos := hCpos hv.1
  unfold likelihoodContactNumerator total at hraw
  have hid : (∑ i, w i * (a i / v i)) - ∑ i, w i =
      ∑ i, w i * ((a i - v i) / v i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [(hvpos i).ne']
  rw [← hid]
  linarith
