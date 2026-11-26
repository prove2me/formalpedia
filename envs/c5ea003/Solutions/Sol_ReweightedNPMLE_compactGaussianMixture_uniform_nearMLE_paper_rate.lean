-- Prove2me | solution 1 for ReweightedNPMLE.compactGaussianMixture_uniform_nearMLE_paper_rate
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:17:56.169582+00:00
-- url     : https://prove2.me/submissions/598f0a3d-f8dd-4a88-a666-ee49d1d5996c

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_EuclideanLocationNet
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianFiniteNet
import Definitions.Def_ReweightedNPMLE_GaussianMixtureHellinger
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_GaussianNearMLE
import Definitions.Def_ReweightedNPMLE_GaussianNearMLERate
import Definitions.Def_ReweightedNPMLE_GaussianRadius
import Definitions.Def_ReweightedNPMLE_Hellinger
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Definitions.Def_ReweightedNPMLE_SimplexGrid
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_compactGaussianMixture_uniform_nearMLE_bad_event_bound_entropy_tuned
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianMomentRelativeError_paper_le
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianNearMLE_threshold_256_le
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianNetLogError_256
import Theorems.Thm_ReweightedNPMLE_eventually_gaussianPaper_weightSmall
import Theorems.Thm_ReweightedNPMLE_gaussianKernel_comp_integrable_prod
import Theorems.Thm_ReweightedNPMLE_gaussianMixture_pos
import Theorems.Thm_ReweightedNPMLE_gaussianPaper_failure_bound

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







































/-- Every translated Gaussian kernel integrates to one. -/
theorem integral_gaussianKernel (d : ℕ) (θ : Point d) :
    ∫ x : Point d, gaussianKernel d x θ = 1 := by
  change (∫ x : Point d, gaussianDensity d (x - θ)) = 1
  rw [integral_sub_right_eq_self, integral_gaussianDensity]























end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianMixtureMeasure.
section
/-!
# Gaussian mixtures indexed by probability measures

This module connects the finite-sum Gaussian algebra to the paper's original
parameter space of arbitrary compactly supported mixing laws.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

namespace ReweightedNPMLE









theorem gaussianMixture_integrable
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθ : Measurable θ) :
    Integrable (gaussianMixture μ θ) := by
  exact (gaussianKernel_comp_integrable_prod μ θ hθ).integral_prod_right





theorem integral_gaussianMixture
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθ : Measurable θ) :
    ∫ x : Point d, gaussianMixture μ θ x = 1 := by
  unfold gaussianMixture
  rw [← integral_integral_swap (gaussianKernel_comp_integrable_prod μ θ hθ)]
  simp_rw [integral_gaussianKernel]
  simp



















end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.PolynomialMoments.
section
namespace ReweightedNPMLE

open scoped BigOperators
open Finset Fintype



/-- There are exactly `choose (D + d) d` monomials of total degree at most `D`. -/
theorem card_monomialCoord (d D : ℕ) :
    Fintype.card (MonomialCoord d D) = (D + d).choose d := by
  rw [Sym.card_sym_eq_choose]
  simp only [Fintype.card_fin]
  have h : d + 1 + D - 1 = D + d := by omega
  rw [h, Nat.choose_symm_add]











/-- The ambient dimension of the moment feature is the number of monomials. -/
theorem finrank_monomialFeature (d D : ℕ) :
    Module.finrank ℝ (MonomialCoord d D → ℝ) = (D + d).choose d := by
  rw [Module.finrank_fintype_fun_eq_card, card_monomialCoord]













































































































end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianNearMLE.
section
/-!
# Uniform near-MLE control for compact Gaussian mixtures

This module closes the main interface between the analytic Gaussian-mixture
net and the finite likelihood-ratio test.  Candidates are genuine bundled
probability measures on a compact location set, rather than a finite-mixture
surrogate parameterization.
-/

open scoped BigOperators ENNReal
open MeasureTheory Set

namespace ReweightedNPMLE





theorem compactGaussianMixtureDensity_pos {d : ℕ}
    {K : Set (Point d)} (G : ProbabilityMeasure K) (x : Point d) :
    0 < compactGaussianMixtureDensity G x := by
  exact gaussianMixture_pos (G : Measure K)
    (fun θ : K ↦ (θ : Point d)) measurable_subtype_coe x

theorem compactGaussianMixtureDensity_integrable {d : ℕ}
    {K : Set (Point d)} (G : ProbabilityMeasure K) :
    Integrable (compactGaussianMixtureDensity G) := by
  exact gaussianMixture_integrable (G : Measure K)
    (fun θ : K ↦ (θ : Point d)) measurable_subtype_coe

theorem integral_compactGaussianMixtureDensity {d : ℕ}
    {K : Set (Point d)} (G : ProbabilityMeasure K) :
    ∫ x, compactGaussianMixtureDensity G x = 1 := by
  exact integral_gaussianMixture (G : Measure K)
    (fun θ : K ↦ (θ : Point d)) measurable_subtype_coe





















/-- Both probabilistic tuning parameters are now expressed as exponents.
Taking `r = sqrt (2R)` gives the radius failure term
`2 n d exp(-R)`, while the entropy-calibrated likelihood-test term remains
`exp(-B-1)`. -/
theorem compactGaussianMixture_uniform_nearMLE_bad_event_bound_fully_tuned
    {d L M n : ℕ} (hn : 0 < n)
    (K : Set (Point d))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    {S ε R B : ℝ} (hS : 0 ≤ S) (hε : 0 < ε) (hR : 0 < R)
    (hB : 0 ≤ B)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S)
    (hM : 0 < M)
    (hrelativeHalf : gaussianMomentRelativeError
      (S + Real.sqrt d * Real.sqrt (2 * R)) S L ≤ 1 / 2)
    (hweightSmall : Real.exp
      (2 * ((S + Real.sqrt d * Real.sqrt (2 * R)) * S + S ^ 2 / 2)) *
        (2 * gaussianMomentDimension d L / M) ≤ 1 / 2)
    (Gstar : ProbabilityMeasure K)
    (hnδ : (n : ℝ) * gaussianNetLogError d L M
      (S + Real.sqrt d * Real.sqrt (2 * R)) S ε ≤ 1) :
    (Measure.pi (fun _ : Fin n ↦ volume.withDensity (fun y ↦
      ENNReal.ofReal (compactGaussianMixtureDensity Gstar y)))).real
        {x | ∃ G : ProbabilityMeasure K,
          (∑ i, Real.log (compactGaussianMixtureDensity Gstar (x i))) - 1 ≤
              ∑ i, Real.log (compactGaussianMixtureDensity G (x i)) ∧
          2 * gaussianNetHellingerSqError d L M S ε +
              4 * (Real.log (gaussianNetCardBound d L M S ε) + B + 2) / n <
            hellingerSq volume (compactGaussianMixtureDensity G)
              (compactGaussianMixtureDensity Gstar)} ≤
      2 * n * d * Real.exp (-R) + Real.exp (-B - 1) := by
  let r : ℝ := Real.sqrt (2 * R)
  have h2R : 0 ≤ 2 * R := by positivity
  have hr : 0 < r := by
    exact Real.sqrt_pos.2 (by positivity)
  have hrSq : r ^ 2 = 2 * R := Real.sq_sqrt h2R
  have hmain :=
    compactGaussianMixture_uniform_nearMLE_bad_event_bound_entropy_tuned
      hn K hKcompact hKnonempty hS hε hr hB hKbound hM
      hrelativeHalf hweightSmall Gstar hnδ
  simpa only [r, hrSq, show -(2 * R) / 2 = -R by ring] using hmain



end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianNearMLERate.
section
/-!
# Explicit entropy arithmetic for the Gaussian near-MLE theorem

This module turns the finite Gaussian-mixture net cardinality appearing in
`GaussianNearMLE` into the binomial and logarithmic bounds used in the
paper's rate calculation.  It is kept separate from the probabilistic
argument so that the remaining asymptotic tuning can use a small, explicit
arithmetic interface.
-/

open scoped ENNReal
open Filter Topology MeasureTheory Set

namespace ReweightedNPMLE













































/-- The Gaussian moment dimension is always nonzero. -/
theorem gaussianMomentDimension_pos (d L : ℕ) :
    0 < gaussianMomentDimension d L := by
  change 0 < Module.finrank ℝ (MonomialCoord d (2 * L) → ℝ)
  rw [finrank_monomialFeature]
  exact Nat.choose_pos (by omega)







theorem gaussianPaperEpsilon_pos {n : ℕ} (hn : 0 < n) :
    0 < gaussianPaperEpsilon n := by
  unfold gaussianPaperEpsilon
  positivity

theorem gaussianPaperWeightDenominator_pos
    (d : ℕ) (C : ℝ) {n : ℕ} (hn : 0 < n) :
    0 < gaussianPaperWeightDenominator d C n := by
  unfold gaussianPaperWeightDenominator
  apply Nat.ceil_pos.mpr
  exact mul_pos (by
      exact_mod_cast (gaussianMomentDimension_pos d
        (gaussianPaperMomentOrder C n)))
    (pow_pos (by exact_mod_cast hn) 16)























/-- Numerical specialization used in the final theorem. -/
theorem eventually_gaussianMomentRelativeError_256_le
    (d : ℕ) {S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in Filter.atTop,
      gaussianMomentRelativeError (gaussianPaperSampleRadius d S b n) S
          (gaussianPaperMomentOrder 256 n) ≤ 2 / (n : ℝ) ^ 31 := by
  filter_upwards [eventually_gaussianMomentRelativeError_paper_le d
    (show (0 : ℝ) < 256 by norm_num) hS hb] with n hn
  convert hn using 1
  norm_num [Real.rpow_neg_natCast, zpow_neg, div_eq_mul_inv]
  rfl





theorem eventually_gaussianMomentRelativeError_256_le_half
    (d : ℕ) {S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in Filter.atTop,
      gaussianMomentRelativeError (gaussianPaperSampleRadius d S b n) S
          (gaussianPaperMomentOrder 256 n) ≤ 1 / 2 := by
  filter_upwards [eventually_gaussianMomentRelativeError_256_le d hS hb,
    Filter.eventually_ge_atTop (2 : ℕ)] with n hrel hn
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (4 : ℝ) ≤ (n : ℝ) ^ 31 := by
    calc
      (4 : ℝ) ≤ 2 ^ 31 := by norm_num
      _ ≤ (n : ℝ) ^ 31 := pow_le_pow_left₀ (by norm_num) hnreal 31
  exact hrel.trans (by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 31) (by norm_num)]
    linarith)























end ReweightedNPMLE
end

/-!
# Explicit entropy arithmetic for the Gaussian near-MLE theorem

This module turns the finite Gaussian-mixture net cardinality appearing in
`GaussianNearMLE` into the binomial and logarithmic bounds used in the
paper's rate calculation.  It is kept separate from the probabilistic
argument so that the remaining asymptotic tuning can use a small, explicit
arithmetic interface.
-/

open scoped ENNReal
open Filter Topology MeasureTheory Set

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Paper-rate specialization of the uniform compact Gaussian-mixture
near-MLE theorem.  Uniformly over every mixing law supported on `K`, every
likelihood maximizer up to additive error one has squared Hellinger loss of
order
`(log n / log log n)^d * log n / n`
outside an event of polynomially small probability. -/
theorem solution
    {d : ℕ} (hd : 0 < d)
    (K : Set (Point d)) (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    {S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ Gstar : ProbabilityMeasure K,
      (Measure.pi (fun _ : Fin n ↦ volume.withDensity (fun y ↦
        ENNReal.ofReal (compactGaussianMixtureDensity Gstar y)))).real
          {x | ∃ G : ProbabilityMeasure K,
            (∑ i, Real.log (compactGaussianMixtureDensity Gstar (x i))) - 1 ≤
                ∑ i, Real.log (compactGaussianMixtureDensity G (x i)) ∧
            gaussianPaperRateConstant d b * gaussianPaperLogScale n ^ d *
                Real.log (n : ℝ) / n <
              hellingerSq volume (compactGaussianMixtureDensity G)
                (compactGaussianMixtureDensity Gstar)} ≤
        (2 * (d : ℝ) + 1) * (n : ℝ) ^ (-(b + 2)) := by
  have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gaussianMomentRelativeError_256_le_half d hS hb,
    eventually_gaussianPaper_weightSmall d (C := (256 : ℝ)) hS hb,
    eventually_gaussianNetLogError_256 d hS hb,
    eventually_gaussianNearMLE_threshold_256_le d hS hb,
    hlog.eventually_gt_atTop 0, Filter.eventually_ge_atTop (1 : ℕ)]
      with n hrelative hweight hnδ hthreshold hlogn hn
  intro Gstar
  let L := gaussianPaperMomentOrder 256 n
  let M := gaussianPaperWeightDenominator d 256 n
  let ε := gaussianPaperEpsilon n
  let R := gaussianPaperRadiusExponent b n
  let B := (b + 2) * Real.log (n : ℝ)
  let T := gaussianPaperSampleRadius d S b n
  let rate := gaussianPaperRateConstant d b * gaussianPaperLogScale n ^ d *
    Real.log (n : ℝ) / n
  have hnpos : 0 < n := by omega
  have hε : 0 < ε := by
    dsimp [ε]
    exact gaussianPaperEpsilon_pos hnpos
  have hR : 0 < R := by
    dsimp [R, gaussianPaperRadiusExponent]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hM : 0 < M := by
    dsimp [M]
    exact gaussianPaperWeightDenominator_pos d 256 hnpos
  have hrelative' : gaussianMomentRelativeError T S L ≤ 1 / 2 := by
    simpa only [T, L] using hrelative
  have hweight' : Real.exp (2 * (T * S + S ^ 2 / 2)) *
      (2 * gaussianMomentDimension d L / M) ≤ 1 / 2 := by
    simpa only [T, L, M, gaussianPaperTaylorArgument] using hweight
  have hnδ' : (n : ℝ) * gaussianNetLogError d L M T S ε ≤ 1 := by
    simpa only [T, L, M, ε] using hnδ
  have hthreshold' :
      2 * gaussianNetHellingerSqError d L M S ε +
          4 * (Real.log (gaussianNetCardBound d L M S ε : ℝ) + B + 2) / n ≤
        rate := by
    simpa only [L, M, ε, B, rate] using hthreshold
  have hmain :=
    compactGaussianMixture_uniform_nearMLE_bad_event_bound_fully_tuned
      (d := d) (L := L) (M := M) (n := n) hnpos K hKcompact hKnonempty
      hS hε hR hB hKbound hM hrelative' hweight' Gstar hnδ'
  let ν : Measure (Point d) := volume.withDensity (fun y ↦
    ENNReal.ofReal (compactGaussianMixtureDensity Gstar y))
  letI : IsProbabilityMeasure ν := IsProbabilityMeasure.mk (by
    dsimp [ν]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal
        (compactGaussianMixtureDensity_integrable Gstar)
        (Filter.Eventually.of_forall fun x ↦
          (compactGaussianMixtureDensity_pos Gstar x).le),
      integral_compactGaussianMixtureDensity]
    norm_num)
  let μ : Measure (Fin n → Point d) := Measure.pi (fun _ : Fin n ↦ ν)
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  let badRate : Set (Fin n → Point d) :=
    {x | ∃ G : ProbabilityMeasure K,
      (∑ i, Real.log (compactGaussianMixtureDensity Gstar (x i))) - 1 ≤
          ∑ i, Real.log (compactGaussianMixtureDensity G (x i)) ∧
      rate < hellingerSq volume (compactGaussianMixtureDensity G)
        (compactGaussianMixtureDensity Gstar)}
  let badRaw : Set (Fin n → Point d) :=
    {x | ∃ G : ProbabilityMeasure K,
      (∑ i, Real.log (compactGaussianMixtureDensity Gstar (x i))) - 1 ≤
          ∑ i, Real.log (compactGaussianMixtureDensity G (x i)) ∧
      2 * gaussianNetHellingerSqError d L M S ε +
          4 * (Real.log (gaussianNetCardBound d L M S ε : ℝ) + B + 2) / n <
        hellingerSq volume (compactGaussianMixtureDensity G)
          (compactGaussianMixtureDensity Gstar)}
  have hsubset : badRate ⊆ badRaw := by
    intro x hx
    rcases hx with ⟨G, hnear, hbad⟩
    exact ⟨G, hnear, lt_of_le_of_lt hthreshold' hbad⟩
  have hmain' : μ.real badRaw ≤
      2 * (n : ℝ) * d * Real.exp (-R) + Real.exp (-B - 1) := by
    simpa only [μ, ν, badRaw, L, M, ε, R, B, T,
      gaussianPaperSampleRadius] using hmain
  have hfailure :
      2 * (n : ℝ) * d * Real.exp (-R) + Real.exp (-B - 1) ≤
        (2 * (d : ℝ) + 1) * (n : ℝ) ^ (-(b + 2)) := by
      simpa only [R, B, neg_mul] using gaussianPaper_failure_bound d n hb hn
  change μ.real badRate ≤
    (2 * (d : ℝ) + 1) * (n : ℝ) ^ (-(b + 2))
  exact (measureReal_mono hsubset (by finiteness)).trans (hmain'.trans hfailure)
