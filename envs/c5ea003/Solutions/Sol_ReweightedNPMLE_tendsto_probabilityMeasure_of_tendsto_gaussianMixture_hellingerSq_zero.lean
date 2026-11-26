-- Prove2me | solution 1 for ReweightedNPMLE.tendsto_probabilityMeasure_of_tendsto_gaussianMixture_hellingerSq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:14:18.15748+00:00
-- url     : https://prove2.me/submissions/739e5d7f-f7a0-4746-a7ed-030d4ce7f97d

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Sequences
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_GaussianRadius
import Definitions.Def_ReweightedNPMLE_Hellinger
import Theorems.Thm_ReweightedNPMLE_continuous_gaussianMixture
import Theorems.Thm_ReweightedNPMLE_gaussianKernel_comp_integrable_prod
import Theorems.Thm_ReweightedNPMLE_gaussianMixture_identifiable_of_measurableEmbedding
import Theorems.Thm_ReweightedNPMLE_gaussianMixture_pos
import Theorems.Thm_ReweightedNPMLE_integral_abs_sub_le_two_mul_sqrt_hellingerSq
import Theorems.Thm_ReweightedNPMLE_tendsto_integral_abs_sub_of_ae_tendsto_of_integral_eq_one

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



theorem measurable_gaussianMixture
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθ : Measurable θ) :
    Measurable (gaussianMixture μ θ) :=
  (continuous_gaussianMixture μ θ hθ).measurable

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

-- Inline helpers preserved from ReweightedNPMLE.Hellinger.
section
/-!
# Squared Hellinger distance

This file formalizes the normalization convention used in the manuscript,
`H²(p,q) = ∫ (√p-√q)²`, and its affinity identity.
-/

open MeasureTheory Filter Topology

namespace ReweightedNPMLE























theorem abs_sub_integrable_of_integrable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (p q : Ω → ℝ)
    (hpint : Integrable p μ) (hqint : Integrable q μ) :
    Integrable (fun x ↦ |p x - q x|) μ := by
  exact (hpint.sub hqint).abs

































end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianIdentifiability.
section
/-!
# Identifiability of Gaussian location mixtures

Convolution with a standard Gaussian is injective on probability measures:
its characteristic function is nowhere zero.  Combined with the generative-
law/density identity, this proves identifiability of the mixing law from the
mixture density.
-/

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction

namespace ReweightedNPMLE













/-- Weak convergence of compactly supported mixing laws implies pointwise
convergence of their Gaussian-mixture densities. -/
theorem tendsto_gaussianMixture_eval_of_tendsto_probabilityMeasure
    {d : ℕ} {K : Set (Point d)} (hKcompact : IsCompact K)
    {ι : Type*} {F : Filter ι}
    {Gs : ι → ProbabilityMeasure K} {G : ProbabilityMeasure K}
    (hG : Tendsto Gs F (𝓝 G)) (x : Point d) :
    Tendsto (fun i ↦ gaussianMixture (Gs i : Measure K)
        (fun θ : K ↦ (θ : Point d)) x) F
      (𝓝 (gaussianMixture (G : Measure K)
        (fun θ : K ↦ (θ : Point d)) x)) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
  let f : C(K, ℝ) :=
    ⟨fun θ ↦ gaussianKernel d x (θ : Point d), by
      unfold gaussianKernel
      fun_prop⟩
  let fb : K →ᵇ ℝ := ContinuousMap.equivBoundedOfCompact K ℝ f
  have ht :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hG) fb
  simpa only [gaussianMixture, fb, f,
    ContinuousMap.equivBoundedOfCompact_apply] using ht









end ReweightedNPMLE
end

/-!
# Identifiability of Gaussian location mixtures

Convolution with a standard Gaussian is injective on probability measures:
its characteristic function is nowhere zero.  Combined with the generative-
law/density identity, this proves identifiability of the mixing law from the
mixture density.
-/

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction

open ReweightedNPMLE
open ReweightedNPMLE in
/-- On a compact location set, convergence of Gaussian-mixture densities in
squared Hellinger distance forces weak convergence of the mixing laws.  This
is the consistency bridge used after the paper's risk bound. -/
theorem solution
    {d : ℕ} {K : Set (Point d)} (hKcompact : IsCompact K)
    (Gs : ℕ → ProbabilityMeasure K) (Gstar : ProbabilityMeasure K)
    (hhell : Tendsto (fun n ↦ hellingerSq volume
        (gaussianMixture (Gs n : Measure K) (fun θ : K ↦ (θ : Point d)))
        (gaussianMixture (Gstar : Measure K) (fun θ : K ↦ (θ : Point d))))
      atTop (𝓝 0)) :
    Tendsto Gs atTop (𝓝 Gstar) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
  let θ : K → Point d := fun z ↦ (z : Point d)
  have hθmeas : Measurable θ := measurable_subtype_coe
  have hθemb : MeasurableEmbedding θ :=
    MeasurableEmbedding.subtype_coe hKcompact.measurableSet
  refine isCompact_univ.tendsto_nhds_of_unique_mapClusterPt
    (Filter.Eventually.of_forall fun n ↦ Set.mem_univ (Gs n)) ?_
  intro G _ hGcluster
  rcases hGcluster.tendsto_subseq with ⟨φ, hφmono, hφ⟩
  have hscheffe : Tendsto (fun n ↦ ∫ x,
        |gaussianMixture (Gs (φ n) : Measure K) θ x -
          gaussianMixture (G : Measure K) θ x|)
      atTop (𝓝 0) := by
    apply tendsto_integral_abs_sub_of_ae_tendsto_of_integral_eq_one
    · intro n
      exact (measurable_gaussianMixture (Gs (φ n) : Measure K) θ hθmeas).aestronglyMeasurable
    · exact (measurable_gaussianMixture (G : Measure K) θ hθmeas).aestronglyMeasurable
    · intro n
      exact Filter.Eventually.of_forall fun x ↦
        (gaussianMixture_pos (Gs (φ n) : Measure K) θ hθmeas x).le
    · exact Filter.Eventually.of_forall fun x ↦
        (gaussianMixture_pos (G : Measure K) θ hθmeas x).le
    · intro n
      exact gaussianMixture_integrable (Gs (φ n) : Measure K) θ hθmeas
    · exact gaussianMixture_integrable (G : Measure K) θ hθmeas
    · intro n
      exact integral_gaussianMixture (Gs (φ n) : Measure K) θ hθmeas
    · exact integral_gaussianMixture (G : Measure K) θ hθmeas
    · exact Filter.Eventually.of_forall fun x ↦
        tendsto_gaussianMixture_eval_of_tendsto_probabilityMeasure
          hKcompact hφ x
  have hhellsub : Tendsto (fun n ↦ hellingerSq volume
        (gaussianMixture (Gs (φ n) : Measure K) θ)
        (gaussianMixture (Gstar : Measure K) θ)) atTop (𝓝 0) := by
    simpa only [θ, Function.comp_apply] using hhell.comp hφmono.tendsto_atTop
  have hupper : Tendsto (fun n ↦ 2 * Real.sqrt (hellingerSq volume
        (gaussianMixture (Gs (φ n) : Measure K) θ)
        (gaussianMixture (Gstar : Measure K) θ))) atTop (𝓝 0) := by
    have hsqrt := hhellsub.sqrt
    simpa using hsqrt.const_mul 2
  have hl1star : Tendsto (fun n ↦ ∫ x,
        |gaussianMixture (Gs (φ n) : Measure K) θ x -
          gaussianMixture (Gstar : Measure K) θ x|)
      atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      exact integral_nonneg fun x ↦ abs_nonneg _
    · intro n
      exact integral_abs_sub_le_two_mul_sqrt_hellingerSq volume
        (gaussianMixture (Gs (φ n) : Measure K) θ)
        (gaussianMixture (Gstar : Measure K) θ)
        (measurable_gaussianMixture (Gs (φ n) : Measure K) θ hθmeas).aestronglyMeasurable
        (measurable_gaussianMixture (Gstar : Measure K) θ hθmeas).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x ↦
          (gaussianMixture_pos (Gs (φ n) : Measure K) θ hθmeas x).le)
        (Filter.Eventually.of_forall fun x ↦
          (gaussianMixture_pos (Gstar : Measure K) θ hθmeas x).le)
        (gaussianMixture_integrable (Gs (φ n) : Measure K) θ hθmeas)
        (gaussianMixture_integrable (Gstar : Measure K) θ hθmeas)
        (integral_gaussianMixture (Gs (φ n) : Measure K) θ hθmeas)
        (integral_gaussianMixture (Gstar : Measure K) θ hθmeas)
    · exact hupper
  let c : ℝ := ∫ x,
    |gaussianMixture (G : Measure K) θ x -
      gaussianMixture (Gstar : Measure K) θ x|
  have htri : ∀ n, c ≤
      (∫ x, |gaussianMixture (G : Measure K) θ x -
        gaussianMixture (Gs (φ n) : Measure K) θ x|) +
      ∫ x, |gaussianMixture (Gs (φ n) : Measure K) θ x -
        gaussianMixture (Gstar : Measure K) θ x| := by
    intro n
    have hGint := gaussianMixture_integrable (G : Measure K) θ hθmeas
    have hnint := gaussianMixture_integrable (Gs (φ n) : Measure K) θ hθmeas
    have hstarint := gaussianMixture_integrable (Gstar : Measure K) θ hθmeas
    have hleft := abs_sub_integrable_of_integrable volume
      (gaussianMixture (G : Measure K) θ)
      (gaussianMixture (Gstar : Measure K) θ) hGint hstarint
    have hfirst := abs_sub_integrable_of_integrable volume
      (gaussianMixture (G : Measure K) θ)
      (gaussianMixture (Gs (φ n) : Measure K) θ) hGint hnint
    have hsecond := abs_sub_integrable_of_integrable volume
      (gaussianMixture (Gs (φ n) : Measure K) θ)
      (gaussianMixture (Gstar : Measure K) θ) hnint hstarint
    calc
      c ≤ ∫ x, |gaussianMixture (G : Measure K) θ x -
          gaussianMixture (Gs (φ n) : Measure K) θ x| +
          |gaussianMixture (Gs (φ n) : Measure K) θ x -
            gaussianMixture (Gstar : Measure K) θ x| := by
        dsimp [c]
        apply integral_mono_ae hleft (hfirst.add hsecond)
        exact Filter.Eventually.of_forall fun x ↦ by
          calc
            |gaussianMixture (G : Measure K) θ x -
                gaussianMixture (Gstar : Measure K) θ x| =
              |(gaussianMixture (G : Measure K) θ x -
                  gaussianMixture (Gs (φ n) : Measure K) θ x) +
                (gaussianMixture (Gs (φ n) : Measure K) θ x -
                  gaussianMixture (Gstar : Measure K) θ x)| := by congr 1 <;> ring
            _ ≤ _ := abs_add_le _ _
      _ = (∫ x, |gaussianMixture (G : Measure K) θ x -
            gaussianMixture (Gs (φ n) : Measure K) θ x|) +
          ∫ x, |gaussianMixture (Gs (φ n) : Measure K) θ x -
            gaussianMixture (Gstar : Measure K) θ x| :=
        integral_add hfirst hsecond
  have hsum : Tendsto (fun n ↦
      (∫ x, |gaussianMixture (G : Measure K) θ x -
        gaussianMixture (Gs (φ n) : Measure K) θ x|) +
      ∫ x, |gaussianMixture (Gs (φ n) : Measure K) θ x -
        gaussianMixture (Gstar : Measure K) θ x|) atTop (𝓝 0) := by
    have hfirst : Tendsto (fun n ↦ ∫ x,
        |gaussianMixture (G : Measure K) θ x -
          gaussianMixture (Gs (φ n) : Measure K) θ x|) atTop (𝓝 0) := by
      simpa only [abs_sub_comm] using hscheffe
    simpa using hfirst.add hl1star
  have hcle : c ≤ 0 := ge_of_tendsto hsum (Filter.Eventually.of_forall htri)
  have hcge : 0 ≤ c := by
    dsimp [c]
    exact integral_nonneg fun x ↦ abs_nonneg _
  have hc : c = 0 := le_antisymm hcle hcge
  have hdiffint : Integrable (fun x ↦
      |gaussianMixture (G : Measure K) θ x -
        gaussianMixture (Gstar : Measure K) θ x|) volume :=
    abs_sub_integrable_of_integrable volume
      (gaussianMixture (G : Measure K) θ)
      (gaussianMixture (Gstar : Measure K) θ)
      (gaussianMixture_integrable (G : Measure K) θ hθmeas)
      (gaussianMixture_integrable (Gstar : Measure K) θ hθmeas)
  have habs : (fun x ↦
      |gaussianMixture (G : Measure K) θ x -
        gaussianMixture (Gstar : Measure K) θ x|) =ᵐ[volume] 0 := by
    apply (integral_eq_zero_iff_of_nonneg (fun x ↦ abs_nonneg _) hdiffint).mp
    exact hc
  have hae : gaussianMixture (G : Measure K) θ =ᵐ[volume]
      gaussianMixture (Gstar : Measure K) θ := by
    filter_upwards [habs] with x hx
    simpa only [Pi.zero_apply, abs_eq_zero, sub_eq_zero] using hx
  apply ProbabilityMeasure.toMeasure_injective
  exact gaussianMixture_identifiable_of_measurableEmbedding
    (G : Measure K) (Gstar : Measure K) θ hθemb hae
