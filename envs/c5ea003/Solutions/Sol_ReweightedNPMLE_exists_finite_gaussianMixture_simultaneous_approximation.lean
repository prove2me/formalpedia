-- Prove2me | solution 1 for ReweightedNPMLE.exists_finite_gaussianMixture_simultaneous_approximation
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:11:09.168716+00:00
-- url     : https://prove2.me/submissions/4b51eabb-0c56-43b9-a8ac-a66fa22839b7

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
import Theorems.Thm_ReweightedNPMLE_abs_gaussianScore_le
import Theorems.Thm_ReweightedNPMLE_continuous_monomialFeature
import Theorems.Thm_ReweightedNPMLE_exists_finite_monomial_moment_matching
import Theorems.Thm_ReweightedNPMLE_gaussian_score_exp_average_error_of_moment_match
import Theorems.Thm_ReweightedNPMLE_hellingerSq_gaussianMixture_finite_moment_matching_le
import Theorems.Thm_ReweightedNPMLE_relative_error_of_exp_lower_bound

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



















theorem continuous_gaussianScore (d : ℕ) :
    Continuous fun z : Point d × Point d ↦ gaussianScore z.1 z.2 := by
  unfold gaussianScore
  fun_prop











/-- The Gaussian translation identity used in Sections 3 and 4 of the manuscript. -/
theorem gaussianKernel_eq_density_mul_exp_score {d : ℕ} (x θ : Point d) :
    gaussianKernel d x θ = gaussianDensity d x * Real.exp (gaussianScore x θ) := by
  rw [gaussianKernel, gaussianDensity, gaussianScore, mul_assoc, ← Real.exp_add]
  congr 1
  rw [norm_sub_sq_real]
  ring































end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.PolynomialMoments.
section
namespace ReweightedNPMLE

open scoped BigOperators
open Finset Fintype













/-- Every finite monomial feature vector is integrable under a finite measure
when the parameter map is measurable and almost surely compactly supported. -/
theorem monomialFeature_integrable_of_compact_support
    {Θ : Type*} [MeasurableSpace Θ] {d D : ℕ}
    (μ : MeasureTheory.Measure Θ) [MeasureTheory.IsFiniteMeasure μ]
    (θ : Θ → Fin d → ℝ) (hθmeas : Measurable θ)
    (K : Set (Fin d → ℝ)) (hKcompact : IsCompact K)
    (hθK : ∀ᵐ a ∂μ, θ a ∈ K) :
    MeasureTheory.Integrable (fun a ↦ monomialFeature d D (θ a)) μ := by
  obtain ⟨C, hC⟩ :=
    (hKcompact.image (continuous_monomialFeature d D)).isBounded.exists_norm_le
  apply MeasureTheory.Integrable.of_bound
    ((continuous_monomialFeature d D).measurable.comp hθmeas).aestronglyMeasurable C
  filter_upwards [hθK] with a ha
  exact hC (monomialFeature d D (θ a)) ⟨θ a, ha, rfl⟩











































































/-- Coordinate and inner-product definitions of the Gaussian score agree. -/
theorem gaussianScore_eq_coordinateGaussianScore
    {d : ℕ} (x θ : Point d) :
    gaussianScore x θ =
      coordinateGaussianScore (fun i ↦ x i) (fun i ↦ θ i) := by
  rw [gaussianScore, coordinateGaussianScore, coordinateDot, coordinateNormSq,
    PiLp.inner_apply, EuclideanSpace.real_norm_sq_eq]
  simp only [RCLike.inner_apply, conj_trivial]
  have hdot :
      (∑ i, θ i * x i) = ∑ i, x i * θ i := by
    apply Fintype.sum_congr
    intro i
    ring
  rw [hdot]
  ring













/-- A probability average of exponentials whose scores are bounded below by
`-B` is at least `exp (-B)`. -/
theorem exp_neg_bound_le_gaussian_score_average
    {Θ : Type*} [MeasurableSpace Θ] {d : ℕ}
    (μ : MeasureTheory.Measure Θ) [MeasureTheory.IsProbabilityMeasure μ]
    (θ : Θ → Fin d → ℝ) (x : Fin d → ℝ) {B : ℝ}
    (hθB : ∀ᵐ a ∂μ, |coordinateGaussianScore x (θ a)| ≤ B)
    (hexp : MeasureTheory.Integrable
      (fun a ↦ Real.exp (coordinateGaussianScore x (θ a))) μ) :
    Real.exp (-B) ≤ ∫ a, Real.exp (coordinateGaussianScore x (θ a)) ∂μ := by
  have hmono : (fun _ : Θ ↦ Real.exp (-B)) ≤ᵐ[μ]
      (fun a ↦ Real.exp (coordinateGaussianScore x (θ a))) := by
    filter_upwards [hθB] with a ha
    exact Real.exp_le_exp.mpr (neg_le_of_abs_le ha)
  have h := MeasureTheory.integral_mono_ae
    (MeasureTheory.integrable_const (c := Real.exp (-B))) hexp hmono
  simpa only [MeasureTheory.integral_const, MeasureTheory.probReal_univ,
    one_smul] using h





















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







/-- Exact factorization of a finite Gaussian mixture into the centered
Gaussian density and its exponential-score normalizer. -/
theorem finiteGaussianMixture_eq_density_mul_score_sum
    {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (θ : ι → Point d) (x : Point d) :
    finiteGaussianMixture w θ x = gaussianDensity d x *
      ∑ i, w i * Real.exp (gaussianScore x (θ i)) := by
  unfold finiteGaussianMixture
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [gaussianKernel_eq_density_mul_exp_score]
  ring





















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
/-- One Carathéodory mixture simultaneously supplies the global Hellinger
approximation and the uniform local relative-density approximation used in
the finite likelihood-net construction. -/
theorem solution
    {d L : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : MeasureTheory.Measure Θ) [MeasureTheory.IsProbabilityMeasure μ]
    (ϑ : Θ → Point d) (hϑmeas : Measurable ϑ)
    (K X : Set (Point d))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hϑK : ∀ a, ϑ a ∈ K)
    {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) (hXbound : ∀ x ∈ X, ‖x‖ ≤ T) :
    ∃ (w : Fin (Module.finrank ℝ
          (MonomialCoord d (2 * L) → ℝ) + 1) → ℝ)
      (z : Fin (Module.finrank ℝ
          (MonomialCoord d (2 * L) → ℝ) + 1) → Point d),
      w ∈ stdSimplex ℝ
        (Fin (Module.finrank ℝ (MonomialCoord d (2 * L) → ℝ) + 1)) ∧
      (∀ i, z i ∈ K) ∧
      hellingerSq MeasureTheory.volume (gaussianMixture μ ϑ)
          (finiteGaussianMixture w z) ≤
        (4 * (Real.exp (S ^ 2) * (S ^ 2) ^ (2 * L + 1) /
          (2 * L + 1).factorial)) ^ (1 / 2 : ℝ) ∧
      ∀ x ∈ X,
        |finiteGaussianMixture w z x / gaussianMixture μ ϑ x - 1| ≤
          2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
            ((T * S + S ^ 2 / 2) ^ (L + 1) / (L + 1).factorial) := by
  let B := T * S + S ^ 2 / 2
  let toCoord : Point d → (Fin d → ℝ) := fun u i ↦ u i
  let Kc : Set (Fin d → ℝ) := toCoord '' K
  have htoCoord : Continuous toCoord := by
    unfold toCoord
    fun_prop
  have hKccompact : IsCompact Kc := hKcompact.image htoCoord
  have hKcnonempty : Kc.Nonempty := hKnonempty.image toCoord
  have hϑKae : ∀ᵐ a ∂μ, ϑ a ∈ K := Filter.Eventually.of_forall hϑK
  have hϑKcae : ∀ᵐ a ∂μ, toCoord (ϑ a) ∈ Kc := by
    filter_upwards [hϑKae] with a ha
    exact ⟨ϑ a, ha, rfl⟩
  have hint : MeasureTheory.Integrable
      (fun a ↦ monomialFeature d (2 * L) (toCoord (ϑ a))) μ :=
    monomialFeature_integrable_of_compact_support
      μ (fun a ↦ toCoord (ϑ a)) (htoCoord.measurable.comp hϑmeas)
        Kc hKccompact hϑKcae
  obtain ⟨w, zc, hw, hzcK, hmom⟩ :=
    exists_finite_monomial_moment_matching
      μ (fun a ↦ toCoord (ϑ a)) Kc hKccompact hKcnonempty hϑKcae hint
  have hchoice : ∀ i, ∃ z, z ∈ K ∧ toCoord z = zc i := by
    intro i
    rcases hzcK i with ⟨z, hzK, hz⟩
    exact ⟨z, hzK, hz⟩
  choose z hzK hz using hchoice
  have hmomPoint :
      ∑ i, w i • monomialFeature d (2 * L) (fun r ↦ z i r) =
        ∫ a, monomialFeature d (2 * L) (fun r ↦ ϑ a r) ∂μ := by
    change ∑ i, w i • monomialFeature d (2 * L) (toCoord (z i)) =
      ∫ a, monomialFeature d (2 * L) (toCoord (ϑ a)) ∂μ
    simpa only [hz] using hmom
  have hH := hellingerSq_gaussianMixture_finite_moment_matching_le
    μ ϑ hϑmeas w z hw.1 hw.2 hint hmomPoint hS
      (fun a ↦ hKbound (ϑ a) (hϑK a))
      (fun i ↦ hKbound (z i) (hzK i))
  refine ⟨w, z, hw, hzK, ?_, ?_⟩
  · simpa only [Nat.mul_add, Nat.add_eq, Nat.cast_ofNat] using hH
  · intro x hxX
    have hB : 0 ≤ B := by
      dsimp only [B]
      positivity
    have hscorePoint (u : Point d) (hu : u ∈ K) :
        |gaussianScore x u| ≤ B := by
      simpa only [B] using
        abs_gaussianScore_le hT hS (hXbound x hxX) (hKbound u hu)
    have hexpOriginal : MeasureTheory.Integrable
        (fun a ↦ Real.exp (gaussianScore x (ϑ a))) μ := by
      apply MeasureTheory.Integrable.of_bound
        (((Real.continuous_exp.comp (continuous_gaussianScore d)).measurable.comp
          (measurable_const.prodMk hϑmeas)).aestronglyMeasurable)
        (Real.exp B)
      exact Filter.Eventually.of_forall fun a ↦ by
        change |Real.exp (gaussianScore x (ϑ a))| ≤ Real.exp B
        rw [abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr
          ((le_abs_self _).trans (hscorePoint (ϑ a) (hϑK a)))
    have hscorec : ∀ u ∈ Kc,
        |coordinateGaussianScore (fun i ↦ x i) u| ≤ B := by
      rintro u ⟨y, hyK, rfl⟩
      simpa only [toCoord, gaussianScore_eq_coordinateGaussianScore] using
        hscorePoint y hyK
    have hexpc : MeasureTheory.Integrable
        (fun a ↦ Real.exp
          (coordinateGaussianScore (fun i ↦ x i) (toCoord (ϑ a)))) μ := by
      apply hexpOriginal.congr
      exact Filter.Eventually.of_forall fun a ↦ by
        simpa only [toCoord] using
          congrArg Real.exp (gaussianScore_eq_coordinateGaussianScore x (ϑ a))
    have hzB : ∀ i,
        |coordinateGaussianScore (fun j ↦ x j) (zc i)| ≤ B :=
      fun i ↦ hscorec (zc i) (hzcK i)
    have hϑB : ∀ᵐ a ∂μ,
        |coordinateGaussianScore (fun j ↦ x j) (toCoord (ϑ a))| ≤ B := by
      filter_upwards [hϑKcae] with a ha
      exact hscorec (toCoord (ϑ a)) ha
    have habs := gaussian_score_exp_average_error_of_moment_match
      μ (fun a ↦ toCoord (ϑ a)) w zc hw hint hmom
        (fun i ↦ x i) hB hzB hϑB hexpc
    have hlower := exp_neg_bound_le_gaussian_score_average
      μ (fun a ↦ toCoord (ϑ a)) (fun i ↦ x i) hϑB hexpc
    have herror :
        |(∑ i, w i * Real.exp
            (coordinateGaussianScore (fun j ↦ x j) (zc i))) -
          ∫ a, Real.exp
            (coordinateGaussianScore (fun j ↦ x j) (toCoord (ϑ a))) ∂μ| ≤
          2 * Real.exp B * (B ^ (L + 1) / (L + 1).factorial) := by
      calc
        _ ≤ 2 * (Real.exp B * B ^ (L + 1) / (L + 1).factorial) := habs
        _ = 2 * Real.exp B * (B ^ (L + 1) / (L + 1).factorial) := by ring
    have hrel := relative_error_of_exp_lower_bound
      (a := ∑ i, w i * Real.exp
        (coordinateGaussianScore (fun j ↦ x j) (zc i)))
      (b := ∫ a, Real.exp
        (coordinateGaussianScore (fun j ↦ x j) (toCoord (ϑ a))) ∂μ)
      (B := B) (r := B ^ (L + 1) / (L + 1).factorial) hlower herror
    have hsum :
        (∑ i, w i * Real.exp
          (coordinateGaussianScore (fun j ↦ x j) (zc i))) =
          ∑ i, w i * Real.exp (gaussianScore x (z i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← hz i, ← gaussianScore_eq_coordinateGaussianScore]
    have hintEq :
        (∫ a, Real.exp
          (coordinateGaussianScore (fun i ↦ x i) (toCoord (ϑ a))) ∂μ) =
          ∫ a, Real.exp (gaussianScore x (ϑ a)) ∂μ := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall fun a ↦ by
        simpa only [toCoord] using
          (congrArg Real.exp
            (gaussianScore_eq_coordinateGaussianScore x (ϑ a))).symm
    rw [hsum, hintEq] at hrel
    have hden : gaussianMixture μ ϑ x = gaussianDensity d x *
        ∫ a, Real.exp (gaussianScore x (ϑ a)) ∂μ := by
      unfold gaussianMixture
      simp_rw [gaussianKernel_eq_density_mul_exp_score]
      exact MeasureTheory.integral_const_mul _ _
    rw [finiteGaussianMixture_eq_density_mul_score_sum, hden,
      mul_div_mul_left _ _ (gaussianDensity_pos d x).ne']
    simpa only [B] using hrel
