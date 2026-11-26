-- Prove2me | solution 1 for ReweightedNPMLE.multiplicativeChange_injOn_of_monotone
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:02:10.220667+00:00
-- url     : https://prove2.me/submissions/a38884b3-a2ea-48b8-a31d-5a6dbec7d4a9

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_DirichletIndependence
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Injective change of variables for determinant moments

This file packages the precise area-formula step used by the paper's
determinant-moment argument.  If an injective differentiable map sends a
localized event into a probability density, its density-weighted Jacobian
has integral at most one.  A pointwise Jacobian/density comparison then
transfers that bound to the desired random variable.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

open ReweightedNPMLE
open ReweightedNPMLE in
/-- A coordinatewise multiplicative perturbation is injective on a positive
set whenever its perturbation field is monotone.  This is the injectivity
argument in the paper's change of variables: equality after perturbation
makes every monotonicity summand nonpositive, so monotonicity forces every
one of them to vanish. -/
theorem solution
    {n : ℕ} {s : Set (Fin n → ℝ)}
    (t : (Fin n → ℝ) → (Fin n → ℝ))
    (hw : ∀ w ∈ s, ∀ i, 0 < w i)
    (htpos : ∀ w ∈ s, ∀ i, 0 < 1 + t w i)
    (hmono : ∀ w ∈ s, ∀ v ∈ s,
      0 ≤ ∑ i, (w i - v i) * (t w i - t v i)) :
    Set.InjOn (fun w i ↦ w i * (1 + t w i)) s := by
  intro w hws v hvs hF
  have hcoord (i : Fin n) :
      w i * (1 + t w i) = v i * (1 + t v i) := congrFun hF i
  have hnonpos (i : Fin n) :
      (w i - v i) * (t w i - t v i) ≤ 0 := by
    rcases le_total (t w i) (t v i) with huv | hvu
    · have hvw : v i ≤ w i := by
        by_contra hn
        have hwv : w i < v i := lt_of_not_ge hn
        have hfac : 1 + t w i ≤ 1 + t v i := by linarith
        have hlt : w i * (1 + t w i) < v i * (1 + t v i) :=
          (mul_lt_mul_of_pos_right hwv (htpos w hws i)).trans_le
            (mul_le_mul_of_nonneg_left hfac (hw v hvs i).le)
        exact (ne_of_lt hlt) (hcoord i)
      exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hvw) (sub_nonpos.mpr huv)
    · have hwv : w i ≤ v i := by
        by_contra hn
        have hvw : v i < w i := lt_of_not_ge hn
        have hfac : 1 + t v i ≤ 1 + t w i := by linarith
        have hlt : v i * (1 + t v i) < w i * (1 + t w i) :=
          (mul_lt_mul_of_pos_right hvw (htpos v hvs i)).trans_le
            (mul_le_mul_of_nonneg_left hfac (hw w hws i).le)
        exact (ne_of_lt hlt) (hcoord i).symm
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hwv) (sub_nonneg.mpr hvu)
  have hsum : (∑ i, (w i - v i) * (t w i - t v i)) = 0 :=
    le_antisymm (Finset.sum_nonpos fun i _ ↦ hnonpos i) (hmono w hws v hvs)
  have hzero (i : Fin n) : (w i - v i) * (t w i - t v i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonpos (fun i (_hi : i ∈ Finset.univ) ↦ hnonpos i)).mp
      hsum i (Finset.mem_univ i)
  apply funext
  intro i
  rcases mul_eq_zero.mp (hzero i) with hwvi | htvi
  · exact sub_eq_zero.mp hwvi
  · have htwi : t w i = t v i := sub_eq_zero.mp htvi
    have heq := hcoord i
    rw [htwi] at heq
    exact mul_right_cancel₀ (ne_of_gt (htpos v hvs i)) heq
