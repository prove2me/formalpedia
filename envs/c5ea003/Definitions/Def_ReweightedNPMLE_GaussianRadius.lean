-- Prove2me | Definitions.Def_ReweightedNPMLE_GaussianRadius
-- name    : ReweightedNPMLE_GaussianRadius
-- status  : Definition
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:24:36.350407+00:00
-- url     : https://prove2.me/theorems/637c7933-882e-5c5b-b7ad-1d685a6d2841
-- title:
--   The generative law of a Gaussian location mixture
-- statement:
--   Given a probability measure \(\mu\) on a measurable parameter space \(\Theta\) and a measurable location map \(\vartheta:\Theta\to\mathbb R^d\), define the Gaussian location-mixture law as the distribution of
--   \[
--   X=\vartheta(A)+Z,\qquad A\sim\mu,\quad Z\sim N(0,I_d),
--   \]
--   where \(A\) and \(Z\) are independent. Equivalently, it is the pushforward of \(\mu\otimes N(0,1)^{\otimes d}\) by addition. The included identities identify the centered Gaussian density with the standard Gaussian law, identify its translates with the location-kernel densities, and show that the mixture law has Lebesgue density
--   \[
--   f_\mu(x)=\int_\Theta(2\pi)^{-d/2}e^{-\|x-\vartheta(a)\|^2/2}\,d\mu(a).
--   \]
--   The sampling map is measurable and the resulting law is a probability measure.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianRadius.lean#L204-L391

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure

/-!
# Gaussian radius bounds

Chernoff and finite-union estimates for the radius event in the likelihood-net
argument.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace ReweightedNPMLE











/-- The density used throughout the formalization induces mathlib's bundled
standard Gaussian law on Euclidean space. -/
theorem withDensity_gaussianDensity_eq_stdGaussian (d : ℕ) :
    volume.withDensity (fun x : Point d ↦ ENNReal.ofReal (gaussianDensity d x)) =
      stdGaussian (Point d) := by
  let ν : Measure (Point d) :=
    volume.withDensity (fun x ↦ ENNReal.ofReal (gaussianDensity d x))
  letI : IsProbabilityMeasure ν := IsProbabilityMeasure.mk (by
    dsimp [ν]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (gaussianDensity_integrable d)
        (Filter.Eventually.of_forall fun x ↦ (gaussianDensity_pos d x).le),
      integral_gaussianDensity]
    norm_num)
  change ν = stdGaussian (Point d)
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_stdGaussian, charFun_apply]
  change (∫ x : Point d,
    Complex.exp ((inner ℝ x t : ℂ) * Complex.I) ∂ν) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    ((continuous_gaussianDensity d).measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall fun x ↦ by simp)]
  simp only [ENNReal.toReal_ofReal (gaussianDensity_pos d _).le,
    Complex.real_smul]
  simp_rw [gaussianDensity, Complex.ofReal_mul, Complex.ofReal_exp]
  simp_rw [mul_assoc, ← Complex.exp_add]
  rw [integral_const_mul]
  have hfun : (fun a : Point d ↦
      Complex.exp ((- ‖a‖ ^ 2 / 2 : ℝ) +
        (inner ℝ a t : ℂ) * Complex.I)) =
      fun a : Point d ↦ Complex.exp
        (-(1 / 2 : ℂ) * (‖a‖ : ℂ) ^ 2 +
          Complex.I * (inner ℝ t a : ℂ)) := by
    funext a
    congr 1
    rw [real_inner_comm a t]
    push_cast
    ring
  rw [hfun, GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (V := Point d) (b := (1 / 2 : ℂ)) (by norm_num) Complex.I t]
  rw [finrank_euclideanSpace_fin]
  have hbase : (↑Real.pi / (1 / 2) : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hbase, show ((d : ℂ) / 2) = (((d : ℝ) / 2 : ℝ) : ℂ) by
    push_cast
    rfl]
  rw [← Complex.ofReal_cpow (by positivity)]
  have hnorm : gaussianConstant d *
      (2 * Real.pi) ^ ((d : ℝ) / 2) = 1 := by
    unfold gaussianConstant
    rw [← Real.rpow_add (by positivity : 0 < 2 * Real.pi)]
    convert Real.rpow_zero (2 * Real.pi) using 1 <;> ring
  rw [← mul_assoc, ← Complex.ofReal_mul, hnorm, Complex.ofReal_one, one_mul]
  congr 1
  rw [Complex.I_sq]
  ring

/-- Translating the standard Gaussian law produces the measure whose density
is the Gaussian location kernel. -/
theorem map_stdGaussian_add_eq_withDensity_gaussianKernel
    {d : ℕ} (θ : Point d) :
    (stdGaussian (Point d)).map (fun z ↦ θ + z) =
      volume.withDensity (fun x ↦ ENNReal.ofReal (gaussianKernel d x θ)) := by
  rw [← withDensity_gaussianDensity_eq_stdGaussian d]
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs,
    withDensity_apply _ (hs.preimage (by fun_prop)), withDensity_apply _ hs]
  let e : Point d ≃ᵐ Point d := MeasurableEquiv.addLeft θ
  have he : MeasurePreserving e volume volume :=
    measurePreserving_add_left volume θ
  have hmeas : Measurable (fun x : Point d ↦
      ENNReal.ofReal (gaussianKernel d x θ)) := by
    exact ((continuous_gaussianKernel d).comp
      (continuous_id.prodMk continuous_const)).measurable.ennreal_ofReal
  have hchange := he.setLIntegral_comp_preimage hs hmeas
  change (∫⁻ x in (fun z : Point d ↦ θ + z) ⁻¹' s,
      ENNReal.ofReal (gaussianDensity d x)) =
    ∫⁻ x in s, ENNReal.ofReal (gaussianKernel d x θ)
  calc
    _ = ∫⁻ x in (fun z : Point d ↦ θ + z) ⁻¹' s,
        ENNReal.ofReal (gaussianKernel d (θ + x) θ) := by
      apply setLIntegral_congr_fun (hs.preimage (by fun_prop))
      intro x _
      unfold gaussianKernel gaussianDensity
      congr 2
      simp
    _ = _ := by
      simpa only [e, MeasurableEquiv.coe_addLeft] using hchange

/-- Sampling law obtained by drawing a location from `μ`, an independent
standard Gaussian vector, and adding them. -/
noncomputable def gaussianLocationMixtureLaw
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) (ϑ : Θ → Point d) : Measure (Point d) :=
  (μ.prod (Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1))).map
    (fun q ↦ ϑ q.1 + WithLp.toLp 2 q.2)

theorem measurable_gaussianLocationMixtureSample
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (ϑ : Θ → Point d) (hϑmeas : Measurable ϑ) :
    Measurable (fun q : Θ × (Fin d → ℝ) ↦
      ϑ q.1 + WithLp.toLp 2 q.2) := by
  fun_prop

/-- The generative Gaussian location-mixture law is exactly the measure
obtained by using `gaussianMixture` as a density with respect to volume. -/
theorem gaussianLocationMixtureLaw_eq_withDensity_gaussianMixture
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (ϑ : Θ → Point d) (hϑmeas : Measurable ϑ) :
    gaussianLocationMixtureLaw μ ϑ =
      volume.withDensity (fun x ↦ ENNReal.ofReal (gaussianMixture μ ϑ x)) := by
  let γd : Measure (Fin d → ℝ) :=
    Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1)
  let shift : Θ × (Fin d → ℝ) → Point d :=
    fun q ↦ ϑ q.1 + WithLp.toLp 2 q.2
  have hshift : Measurable shift :=
    measurable_gaussianLocationMixtureSample ϑ hϑmeas
  ext s hs
  rw [gaussianLocationMixtureLaw, Measure.map_apply hshift hs,
    Measure.prod_apply (hs.preimage hshift), withDensity_apply _ hs]
  have hslice : ∀ a : Θ,
      γd {z | ϑ a + WithLp.toLp 2 z ∈ s} =
        ∫⁻ x in s, ENNReal.ofReal (gaussianKernel d x (ϑ a)) := by
    intro a
    have hmap : γd.map (fun z ↦ ϑ a + WithLp.toLp 2 z) =
        volume.withDensity
          (fun x ↦ ENNReal.ofReal (gaussianKernel d x (ϑ a))) := by
      rw [show (fun z : Fin d → ℝ ↦ ϑ a + WithLp.toLp 2 z) =
          (fun x : Point d ↦ ϑ a + x) ∘ WithLp.toLp 2 by rfl,
        ← Measure.map_map (measurable_const_add (ϑ a)) (by fun_prop)]
      rw [show γd.map (WithLp.toLp 2) = stdGaussian (Point d) by
        simpa only [γd] using
          (ProbabilityTheory.map_pi_eq_stdGaussian (ι := Fin d)),
        map_stdGaussian_add_eq_withDensity_gaussianKernel]
    have hsmap := congrArg (fun m : Measure (Point d) ↦ m s) hmap
    have hza : Measurable (fun z : Fin d → ℝ ↦
        ϑ a + WithLp.toLp 2 z) :=
      (measurable_const_add (ϑ a)).comp (by fun_prop)
    change (γd.map (fun z ↦ ϑ a + WithLp.toLp 2 z)) s = _ at hsmap
    rw [Measure.map_apply hza hs] at hsmap
    change γd ((fun z ↦ ϑ a + WithLp.toLp 2 z) ⁻¹' s) =
      (volume.withDensity
        (fun x ↦ ENNReal.ofReal (gaussianKernel d x (ϑ a)))) s at hsmap
    rw [withDensity_apply _ hs] at hsmap
    exact hsmap
  change (∫⁻ a, γd {z | ϑ a + WithLp.toLp 2 z ∈ s} ∂μ) = _
  simp_rw [hslice]
  let F : Θ → Point d → ℝ≥0∞ := fun a x ↦
    s.indicator (fun y ↦ ENNReal.ofReal (gaussianKernel d y (ϑ a))) x
  have hFmeas : Measurable (Function.uncurry F) := by
    apply Measurable.indicator
    · exact ((continuous_gaussianKernel d).measurable.comp
        (measurable_snd.prodMk (hϑmeas.comp measurable_fst))).ennreal_ofReal
    · exact hs.preimage measurable_snd
  have hswap := lintegral_lintegral_swap
    (μ := μ) (ν := volume) hFmeas.aemeasurable
  have hmix (x : Point d) :
      ENNReal.ofReal (gaussianMixture μ ϑ x) =
        ∫⁻ a, ENNReal.ofReal (gaussianKernel d x (ϑ a)) ∂μ := by
    unfold gaussianMixture
    exact ofReal_integral_eq_lintegral_ofReal
      (gaussianKernel_comp_integrable μ ϑ hϑmeas x)
      (Filter.Eventually.of_forall fun a ↦
        (gaussianKernel_pos d x (ϑ a)).le)
  calc
    _ = ∫⁻ a, ∫⁻ x, F a x ∂volume ∂μ := by
      simp only [F, lintegral_indicator hs]
    _ = ∫⁻ x, ∫⁻ a, F a x ∂μ ∂volume := hswap
    _ = ∫⁻ x in s, ENNReal.ofReal (gaussianMixture μ ϑ x) := by
      rw [← lintegral_indicator hs]
      apply lintegral_congr
      intro x
      by_cases hx : x ∈ s
      · simp only [F, Set.indicator_of_mem hx]
        exact (hmix x).symm
      · simp only [F, Set.indicator_of_notMem hx, lintegral_zero]

theorem gaussianLocationMixtureLaw_isProbability
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (ϑ : Θ → Point d) (hϑmeas : Measurable ϑ) :
    IsProbabilityMeasure (gaussianLocationMixtureLaw μ ϑ) := by
  exact Measure.isProbabilityMeasure_map
    (measurable_gaussianLocationMixtureSample ϑ hϑmeas).aemeasurable





end ReweightedNPMLE


