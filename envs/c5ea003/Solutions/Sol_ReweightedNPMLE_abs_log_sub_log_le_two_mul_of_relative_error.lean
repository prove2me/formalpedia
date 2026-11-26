-- Prove2me | solution 1 for ReweightedNPMLE.abs_log_sub_log_le_two_mul_of_relative_error
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:52:39.437799+00:00
-- url     : https://prove2.me/submissions/3b070b67-5d6d-44cd-9b09-db2ae1d903c1

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

-- Inline helpers preserved from ReweightedNPMLE.Localization.
section
/-!
# Radial localization inequalities

Scalar and coordinatewise estimates used by the radial-localization part of the
effective-dimension theorem.
-/

open scoped BigOperators
open Set

namespace ReweightedNPMLE



/-- A direct logarithm bound from the convergent Taylor series. -/
theorem abs_log_one_add_le {u : ℝ} (hu : |u| < 1) :
    |Real.log (1 + u)| ≤ |u| / (1 - |u|) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -u) (by simpa) 0
  simpa using h









end ReweightedNPMLE
end

/-!
# Deterministic Gaussian-mixture likelihood-net estimates

This file proves the local density and log-density estimates used after the
moment-matching step of the finite likelihood-net construction.
-/

open scoped BigOperators RealInnerProductSpace

open ReweightedNPMLE
open ReweightedNPMLE in
/-- A relative error at most `δ ≤ 1/2` implies the standard `2δ`
log-density error. -/
theorem solution
    {a b δ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hrel : |a / b - 1| ≤ δ) :
    |Real.log a - Real.log b| ≤ 2 * δ := by
  let u := a / b - 1
  have hu : |u| ≤ δ := hrel
  have hu1 : |u| < 1 := hu.trans_lt (hδhalf.trans_lt (by norm_num))
  have hden : 0 < 1 - |u| := sub_pos.mpr hu1
  calc
    |Real.log a - Real.log b| = |Real.log (a / b)| := by
      rw [Real.log_div ha.ne' hb.ne']
    _ = |Real.log (1 + u)| := by
      congr 2
      dsimp [u]
      ring
    _ ≤ |u| / (1 - |u|) := abs_log_one_add_le hu1
    _ ≤ 2 * δ := by
      rw [div_le_iff₀ hden]
      nlinarith [abs_nonneg u]
