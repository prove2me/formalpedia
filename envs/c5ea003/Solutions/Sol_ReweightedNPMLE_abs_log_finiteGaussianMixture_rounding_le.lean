-- Prove2me | solution 1 for ReweightedNPMLE.abs_log_finiteGaussianMixture_rounding_le
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:00:08.954286+00:00
-- url     : https://prove2.me/submissions/4adb8bd4-8768-4866-a5b7-864c8a096904

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
import Theorems.Thm_ReweightedNPMLE_abs_finiteGaussianMixture_weight_relative_error_le
import Theorems.Thm_ReweightedNPMLE_abs_log_sub_log_le_two_mul_of_relative_error
import Theorems.Thm_ReweightedNPMLE_finiteGaussianMixture_location_exp_bounds

-- Inline helpers preserved from ReweightedNPMLE.Gaussian.
section
/-!
# Gaussian location-mixture algebra

The manuscript factors a Gaussian translate into a common density and an exponential
score.  This file formalizes that identity and the uniform score bounds used in both the
effective-dimension and finite-net arguments.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

namespace ReweightedNPMLE





























theorem finiteGaussianMixture_pos {d : ℕ} {ι : Type*} [Fintype ι]
    {w : ι → ℝ} (θ : ι → Point d) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) (x : Point d) :
    0 < finiteGaussianMixture w θ x := by
  have hsumpos : 0 < ∑ i, w i := by rw [hsum]; norm_num
  obtain ⟨i, _, hi⟩ :=
    (Finset.sum_pos_iff_of_nonneg fun i (_ : i ∈ Finset.univ) ↦ hw i).mp hsumpos
  unfold finiteGaussianMixture
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (hw j) (gaussianKernel_pos d x (θ j)).le
  · exact ⟨i, Finset.mem_univ i, mul_pos hi (gaussianKernel_pos d x (θ i))⟩

































end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianMixtureNet.
section
/-!
# Deterministic Gaussian-mixture likelihood-net estimates

This file proves the local density and log-density estimates used after the
moment-matching step of the finite likelihood-net construction.
-/

open scoped BigOperators RealInnerProductSpace

namespace ReweightedNPMLE





/-- Two-sided multiplicative exponential bounds imply an additive log bound. -/
theorem abs_log_sub_log_le_of_exp_bounds {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hlower : Real.exp (-c) * b ≤ a)
    (hupper : a ≤ Real.exp c * b) :
    |Real.log a - Real.log b| ≤ c := by
  have hlowerLog : Real.log (Real.exp (-c) * b) ≤ Real.log a :=
    (Real.log_le_log_iff (mul_pos (Real.exp_pos _) hb) ha).2 hlower
  have hupperLog : Real.log a ≤ Real.log (Real.exp c * b) :=
    (Real.log_le_log_iff ha (mul_pos (Real.exp_pos _) hb)).2 hupper
  rw [Real.log_mul (Real.exp_ne_zero _) hb.ne', Real.log_exp] at hlowerLog hupperLog
  rw [abs_le]
  constructor <;> linarith







/-- Uniform local log-density error caused by rounding the locations of a
finite probability mixture. -/
theorem abs_log_finiteGaussianMixture_location_rounding_le
    {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (θ η : ι → Point d) (x : Point d)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    {T S ε : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hε : 0 ≤ ε)
    (hx : ‖x‖ ≤ T) (hθ : ∀ i, ‖θ i‖ ≤ S) (hη : ∀ i, ‖η i‖ ≤ S)
    (hθη : ∀ i, ‖θ i - η i‖ ≤ ε) :
    |Real.log (finiteGaussianMixture w η x) -
        Real.log (finiteGaussianMixture w θ x)| ≤ (T + S) * ε := by
  have hb := finiteGaussianMixture_location_exp_bounds
    w θ η x hw hT hS hε hx hθ hη hθη
  exact abs_log_sub_log_le_of_exp_bounds
    (finiteGaussianMixture_pos η hw hwsum x)
    (finiteGaussianMixture_pos θ hw hwsum x) hb.1 hb.2



/-- Uniform local log-density error caused by rounding only the weights. -/
theorem abs_log_finiteGaussianMixture_weight_rounding_le
    {d : ℕ} {ι : Type*} [Fintype ι]
    (w v : ι → ℝ) (θ : ι → Point d) (x : Point d)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (hwsum : ∑ i, w i = 1) (hvsum : ∑ i, v i = 1)
    {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hx : ‖x‖ ≤ T) (hθ : ∀ i, ‖θ i‖ ≤ S)
    (hsmall : Real.exp (2 * (T * S + S ^ 2 / 2)) *
      ∑ i, |v i - w i| ≤ 1 / 2) :
    |Real.log (finiteGaussianMixture v θ x) -
        Real.log (finiteGaussianMixture w θ x)| ≤
      2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
        ∑ i, |v i - w i| := by
  let δ := Real.exp (2 * (T * S + S ^ 2 / 2)) * ∑ i, |v i - w i|
  have hδ : 0 ≤ δ := by positivity
  have hlog := abs_log_sub_log_le_two_mul_of_relative_error
    (finiteGaussianMixture_pos θ hv hvsum x)
    (finiteGaussianMixture_pos θ hw hwsum x) hδ
    (by simpa only [δ] using hsmall)
    (abs_finiteGaussianMixture_weight_relative_error_le
      w v θ x hw hwsum hT hS hx hθ)
  simpa only [δ, mul_assoc] using hlog











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
/-- Combined local log-density estimate for simultaneously rounding the
locations and the weights of a finite probability mixture. -/
theorem solution
    {d : ℕ} {ι : Type*} [Fintype ι]
    (w v : ι → ℝ) (θ η : ι → Point d) (x : Point d)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (hwsum : ∑ i, w i = 1) (hvsum : ∑ i, v i = 1)
    {T S ε : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hε : 0 ≤ ε)
    (hx : ‖x‖ ≤ T) (hθ : ∀ i, ‖θ i‖ ≤ S) (hη : ∀ i, ‖η i‖ ≤ S)
    (hθη : ∀ i, ‖θ i - η i‖ ≤ ε)
    (hsmall : Real.exp (2 * (T * S + S ^ 2 / 2)) *
      ∑ i, |v i - w i| ≤ 1 / 2) :
    |Real.log (finiteGaussianMixture v η x) -
        Real.log (finiteGaussianMixture w θ x)| ≤
      (T + S) * ε +
        2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
          ∑ i, |v i - w i| := by
  have hloc := abs_log_finiteGaussianMixture_location_rounding_le
    w θ η x hw hwsum hT hS hε hx hθ hη hθη
  have hmass := abs_log_finiteGaussianMixture_weight_rounding_le
    w v η x hw hv hwsum hvsum hT hS hx hη hsmall
  calc
    |Real.log (finiteGaussianMixture v η x) -
        Real.log (finiteGaussianMixture w θ x)| =
        |(Real.log (finiteGaussianMixture v η x) -
            Real.log (finiteGaussianMixture w η x)) +
          (Real.log (finiteGaussianMixture w η x) -
            Real.log (finiteGaussianMixture w θ x))| := by ring
    _ ≤ |Real.log (finiteGaussianMixture v η x) -
          Real.log (finiteGaussianMixture w η x)| +
        |Real.log (finiteGaussianMixture w η x) -
          Real.log (finiteGaussianMixture w θ x)| := abs_add_le _ _
    _ ≤ 2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
          ∑ i, |v i - w i| + (T + S) * ε := add_le_add hmass hloc
    _ = (T + S) * ε +
        2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
          ∑ i, |v i - w i| := by ring
