-- Prove2me | solution 1 for ReweightedNPMLE.gammaEffectiveEvent_localization_bounds
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:10:40.567181+00:00
-- url     : https://prove2.me/submissions/729b5769-bc18-4a1d-9948-7091db98a5cf

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_DirichletIndependence
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_GammaEffectiveEvent
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianWidth
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_euclidean_norm_le_sqrt_card_mul

/-!
# Common Gamma concentration and localization event

The projected-energy and maximum-coordinate bounds hold jointly with
failure probability at most `2 exp(-q)`.  Explicit scale conditions imply
all radial localization hypotheses and the sharp `alpha E <= 2` width
cost bound.
-/

open Set Filter MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Topology

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution {n r : ℕ}
    {α q η : ℝ} (hα : 0 < α) (hQ : 0 ≤ effectiveQ n q) (hN : 0 ≤ effectiveN r q)
    (hη : 0 ≤ η) (hwidthScale : η * Real.sqrt (α * (n : ℝ) * effectiveQ n q) ≤ 1)
    (hαQ : 1024 * effectiveQ n q ≤ α)
    (hαN : 2359296 * effectiveN r q ≤ α) (hα₀ : 12288 ≤ α)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    {w : Fin n → ℝ} (hw : w ∈ gammaEffectiveEvent V r α q) :
    let A := ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖
    let E := η * ‖WithLp.toLp 2 (fun i ↦ w i - 1)‖
    (∀ i, |w i - 1| ≤ 1 / 16) ∧ w ∈ positiveVectors n ∧
    α * A ^ 2 ≤ 16 * effectiveN r q ∧ α * E ≤ 2 ∧
    A ≤ (1 / 16 : ℝ) / 24 ∧ E ≤ (1 / 16 : ℝ) ^ 2 / 24 := by
  let A := ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖
  let X := ‖WithLp.toLp 2 (fun i ↦ w i - 1)‖
  let E := η * X
  let t := 2 * Real.sqrt (effectiveQ n q / α)
  have hradius : t ≤ 1 / 16 := by
    have hdiv : effectiveQ n q / α ≤ 1 / 1024 :=
      (div_le_iff₀ hα).mpr (by linarith)
    have hs := Real.sq_sqrt (div_nonneg hQ hα.le)
    dsimp [t]
    nlinarith [Real.sqrt_nonneg (effectiveQ n q / α)]
  have hw16 : ∀ i, |w i - 1| ≤ 1 / 16 := fun i ↦ (hw.1 i).trans hradius
  have hwpos : w ∈ positiveVectors n := by
    intro i
    have hi := neg_le_of_abs_le (hw16 i)
    linarith
  have hAsq : α * A ^ 2 ≤ 16 * effectiveN r q := by
    have hp := hw.2
    have hsq := mul_le_mul hp hp (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Real.sqrt_nonneg _))
    convert hsq using 1
    · calc
        α * A ^ 2 = (Real.sqrt α) ^ 2 * A ^ 2 := by rw [Real.sq_sqrt hα.le]
        _ = _ := by dsimp [A]; ring
    · rw [show (4 * Real.sqrt (effectiveN r q)) * (4 * Real.sqrt (effectiveN r q)) =
        16 * (Real.sqrt (effectiveN r q)) ^ 2 by ring, Real.sq_sqrt hN]
  have hX : X ≤ Real.sqrt n * t :=
    euclidean_norm_le_sqrt_card_mul (WithLp.toLp 2 (fun i ↦ w i - 1))
      (by dsimp [t]; positivity) (fun i ↦ hw.1 i)
  have hid : α * (Real.sqrt n * t) = 2 * Real.sqrt (α * (n : ℝ) * effectiveQ n q) := by
    dsimp [t]
    rw [Real.sqrt_div hQ, Real.sqrt_mul (mul_nonneg hα.le (Nat.cast_nonneg n)),
      Real.sqrt_mul hα.le]
    calc
      α * (Real.sqrt n * (2 * (Real.sqrt (effectiveQ n q) / Real.sqrt α))) =
          2 * (α / Real.sqrt α) * Real.sqrt n * Real.sqrt (effectiveQ n q) := by ring
      _ = 2 * (Real.sqrt α * Real.sqrt n) * Real.sqrt (effectiveQ n q) := by
        rw [Real.div_sqrt]
        ring
      _ = _ := by ring
  have hEscaled : α * E ≤ 2 := by
    calc
      α * E ≤ η * (α * (Real.sqrt n * t)) := by
        dsimp [E]
        nlinarith [mul_le_mul_of_nonneg_left hX (mul_nonneg hα.le hη)]
      _ = 2 * (η * Real.sqrt (α * (n : ℝ) * effectiveQ n q)) := by rw [hid]; ring
      _ ≤ 2 := by linarith
  have hAlocal : A ≤ (1 / 16 : ℝ) / 24 := by
    have hh : α * A ^ 2 ≤ α * ((1 / 16 : ℝ) / 24) ^ 2 := by
      nlinarith [hαN]
    have hs := (mul_le_mul_iff_right₀ hα).mp hh
    nlinarith [norm_nonneg (V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1)))]
  have hElocal : E ≤ (1 / 16 : ℝ) ^ 2 / 24 := by
    have hh : α * E ≤ α * ((1 / 16 : ℝ) ^ 2 / 24) := by linarith
    exact (mul_le_mul_iff_right₀ hα).mp hh
  exact ⟨hw16, hwpos, hAsq, hEscaled, hAlocal, hElocal⟩
