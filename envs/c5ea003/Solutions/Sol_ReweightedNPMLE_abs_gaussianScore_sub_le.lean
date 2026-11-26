-- Prove2me | solution 1 for ReweightedNPMLE.abs_gaussianScore_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:52:36.411198+00:00
-- url     : https://prove2.me/submissions/910e39fc-74ab-4d54-aa88-7f1ffadd345d

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianMixtureHellinger
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_Hellinger
import Definitions.Def_ReweightedNPMLE_PolynomialMoments

/-!
# Deterministic Gaussian-mixture likelihood-net estimates

This file proves the local density and log-density estimates used after the
moment-matching step of the finite likelihood-net construction.
-/

open scoped BigOperators RealInnerProductSpace

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Moving a Gaussian location by at most `ε` changes its score by at most
`(T + S) ε` on the radius-`T` observation ball when both locations lie in the
radius-`S` parameter ball. -/
theorem solution {d : ℕ} (x θ η : Point d)
    {T S ε : ℝ} (hT : 0 ≤ T) (_hS : 0 ≤ S) (hε : 0 ≤ ε)
    (hx : ‖x‖ ≤ T) (hθ : ‖θ‖ ≤ S) (hη : ‖η‖ ≤ S)
    (hθη : ‖θ - η‖ ≤ ε) :
    |gaussianScore x θ - gaussianScore x η| ≤ (T + S) * ε := by
  have hinner : |inner ℝ x (θ - η)| ≤ T * ε := by
    exact (abs_real_inner_le_norm x (θ - η)).trans
      (mul_le_mul hx hθη (norm_nonneg _) hT)
  have hnormsum : ‖θ‖ + ‖η‖ ≤ 2 * S := by linarith
  have hnormdiff : |‖θ‖ ^ 2 - ‖η‖ ^ 2| ≤ 2 * S * ε := by
    calc
      |‖θ‖ ^ 2 - ‖η‖ ^ 2| = |‖θ‖ - ‖η‖| * (‖θ‖ + ‖η‖) := by
        rw [show ‖θ‖ ^ 2 - ‖η‖ ^ 2 =
          (‖θ‖ - ‖η‖) * (‖θ‖ + ‖η‖) by ring, abs_mul,
          abs_of_nonneg (by positivity : 0 ≤ ‖θ‖ + ‖η‖)]
      _ ≤ ‖θ - η‖ * (‖θ‖ + ‖η‖) :=
        mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le θ η) (by positivity)
      _ ≤ ε * (2 * S) :=
        mul_le_mul hθη hnormsum (by positivity) hε
      _ = 2 * S * ε := by ring
  have hscore : gaussianScore x θ - gaussianScore x η =
      inner ℝ x (θ - η) - (‖θ‖ ^ 2 - ‖η‖ ^ 2) / 2 := by
    simp only [gaussianScore, inner_sub_right]
    ring
  rw [hscore]
  calc
    |inner ℝ x (θ - η) - (‖θ‖ ^ 2 - ‖η‖ ^ 2) / 2| ≤
        |inner ℝ x (θ - η)| + |(‖θ‖ ^ 2 - ‖η‖ ^ 2) / 2| :=
      abs_sub _ _
    _ = |inner ℝ x (θ - η)| + |‖θ‖ ^ 2 - ‖η‖ ^ 2| / 2 := by
      rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    _ ≤ T * ε + (2 * S * ε) / 2 :=
      add_le_add hinner (div_le_div_of_nonneg_right hnormdiff (by norm_num))
    _ = (T + S) * ε := by ring
