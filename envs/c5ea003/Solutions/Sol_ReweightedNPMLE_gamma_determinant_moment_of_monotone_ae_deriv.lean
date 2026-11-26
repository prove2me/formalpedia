-- Prove2me | solution 1 for ReweightedNPMLE.gamma_determinant_moment_of_monotone_ae_deriv
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:03:49.537926+00:00
-- url     : https://prove2.me/submissions/fa99d6f2-81f0-42aa-be1e-b55f6ede75b5

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
import Theorems.Thm_ReweightedNPMLE_gamma_density_jacobian_domination_real
import Theorems.Thm_ReweightedNPMLE_multiplicativeChange_injOn_of_monotone
import Theorems.Thm_ReweightedNPMLE_pi_withDensity_prod_eq

-- Inline helpers preserved from ReweightedNPMLE.DirichletIndependence.
section
/-!
# Scale invariance behind Gamma--Dirichlet independence

The normalized Gamma vector is unchanged by a common positive rescaling.
This file first proves the corresponding exact scaling laws for scalar and
finite-product Gamma measures.  These are the measure-theoretic core of the
remaining independence statement in Proposition 2.1.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace ReweightedNPMLE















theorem gammaProductDensity_eq_ofReal (n : ℕ) {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (w : Fin n → ℝ) :
    gammaProductDensity n a r w =
      ENNReal.ofReal (gammaProductDensityReal n a r w) := by
  unfold gammaProductDensity gammaProductDensityReal gammaPDF
  rw [ENNReal.ofReal_prod_of_nonneg]
  intro i hi
  exact gammaPDFReal_nonneg ha hr _





theorem measurable_gammaProductDensity (n : ℕ) (a r : ℝ) :
    Measurable (gammaProductDensity n a r) := by
  unfold gammaProductDensity gammaPDF
  fun_prop

/-- The independent Gamma product has the expected product density with
respect to Lebesgue measure on `ℝⁿ`. -/
theorem gammaProductMeasure_eq_volume_withDensity (n : ℕ) (a r : ℝ) :
    gammaProductMeasure n a r =
      volume.withDensity (gammaProductDensity n a r) := by
  rw [gammaProductMeasure, gammaMeasure, volume_pi]
  exact pi_withDensity_prod_eq
    (fun _i : Fin n ↦ gammaPDF a r)
    (fun _i ↦ (measurable_gammaPDFReal a r).ennreal_ofReal)
    (fun _i _x ↦ ENNReal.ofReal_ne_top)

/-- The product Gamma density integrates to one for positive shape and rate. -/
theorem lintegral_gammaProductDensity_eq_one (n : ℕ)
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∫⁻ w : Fin n → ℝ, gammaProductDensity n a r w ∂volume = 1 := by
  letI : IsProbabilityMeasure (gammaMeasure a r) :=
    isProbabilityMeasure_gammaMeasure ha hr
  letI : IsProbabilityMeasure (gammaProductMeasure n a r) := by
    dsimp [gammaProductMeasure]
    infer_instance
  have h : gammaProductMeasure n a r Set.univ = 1 := measure_univ
  rw [gammaProductMeasure_eq_volume_withDensity,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  exact h























end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.ChangeOfVariables.
section
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

namespace ReweightedNPMLE





/-- `ENNReal` form of `gamma_density_jacobian_domination_real`, ready for
direct use under a Gamma product measure. -/
theorem gamma_density_jacobian_domination
    {n : ℕ} {α c J : ℝ} (hα : 0 < α) (hc : 0 ≤ c) (hJ : 0 ≤ J)
    (w t : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (ht : ∀ i, |t i| ≤ 1 / 8)
    (hdet : (∏ i, (1 + t i)) * c ≤ J) :
    gammaProductDensity n α α w * ENNReal.ofReal
        (c * Real.exp (-α *
          (∑ i, (w i - 1) * t i + ∑ i, (t i) ^ 2))) ≤
      ENNReal.ofReal J * gammaProductDensity n α α
        (fun i ↦ w i * (1 + t i)) := by
  rw [gammaProductDensity_eq_ofReal n hα hα,
    gammaProductDensity_eq_ofReal n hα hα,
    ← ENNReal.ofReal_mul (by
      unfold gammaProductDensityReal
      exact Finset.prod_nonneg fun i _ ↦ gammaPDFReal_nonneg hα hα _),
    ← ENNReal.ofReal_mul hJ]
  exact ENNReal.ofReal_le_ofReal
    (gamma_density_jacobian_domination_real hα hc w t hw ht hdet)

/-- The density-weighted Jacobian of an injective differentiable map over a
measurable set has integral at most the total mass of the target density. -/
theorem lintegral_density_jacobian_le_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    {s : Set E} (hs : MeasurableSet s) {F : E → E}
    {F' : E → E →L[ℝ] E}
    (hF' : ∀ x ∈ s, HasFDerivWithinAt F (F' x) s x)
    (hF : Set.InjOn F s) (p : E → ENNReal)
    (hp : ∫⁻ y, p y ∂volume ≤ 1) :
    ∫⁻ x in s, ENNReal.ofReal |(F' x).det| * p (F x) ∂volume ≤ 1 := by
  rw [← lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hF' hF]
  exact (setLIntegral_le_lintegral (F '' s) p).trans hp

/-- Abstract determinant-moment transfer.  The hypothesis `hdom` is exactly
the pointwise comparison obtained by multiplying the density ratio by the
Jacobian lower bound. -/
theorem lintegral_under_density_le_one_of_jacobian
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]
    {s : Set E} (hs : MeasurableSet s) {F : E → E}
    {F' : E → E →L[ℝ] E}
    (hF' : ∀ x ∈ s, HasFDerivWithinAt F (F' x) s x)
    (hF : Set.InjOn F s) {p Y : E → ENNReal}
    (hpmeas : Measurable p) (hYmeas : Measurable Y)
    (hp : ∫⁻ y, p y ∂volume ≤ 1)
    (hdom : ∀ x ∈ s,
      p x * Y x ≤ ENNReal.ofReal |(F' x).det| * p (F x)) :
    ∫⁻ x in s, Y x ∂volume.withDensity p ≤ 1 := by
  rw [setLIntegral_withDensity_eq_setLIntegral_mul volume hpmeas hYmeas hs]
  exact (setLIntegral_mono' hs hdom).trans
    (lintegral_density_jacobian_le_one hs hF' hF p hp)

/-- Gamma-product specialization of the injective determinant-moment
transfer.  All normalization of the product density is discharged here. -/
theorem gammaProduct_lintegral_le_one_of_jacobian
    {n : ℕ} {α : ℝ} (hα : 0 < α)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s)
    {F : (Fin n → ℝ) → (Fin n → ℝ)}
    {F' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hF' : ∀ x ∈ s, HasFDerivWithinAt F (F' x) s x)
    (hF : Set.InjOn F s) {Y : (Fin n → ℝ) → ENNReal}
    (hYmeas : Measurable Y)
    (hdom : ∀ x ∈ s,
      gammaProductDensity n α α x * Y x ≤
        ENNReal.ofReal |(F' x).det| * gammaProductDensity n α α (F x)) :
    ∫⁻ x in s, Y x ∂gammaProductMeasure n α α ≤ 1 := by
  rw [gammaProductMeasure_eq_volume_withDensity]
  exact lintegral_under_density_le_one_of_jacobian hs hF' hF
    (measurable_gammaProductDensity n α α) hYmeas
    (lintegral_gammaProductDensity_eq_one n hα hα).le hdom

/-- Derivative of the coordinatewise multiplicative change map
`w ↦ w * (1 + t w)`. -/
theorem hasFDerivWithinAt_multiplicativeChange
    {n : ℕ} {s : Set (Fin n → ℝ)}
    {t : (Fin n → ℝ) → (Fin n → ℝ)}
    {t' : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)} {w : Fin n → ℝ}
    (ht : HasFDerivWithinAt t t' s w) :
    HasFDerivWithinAt (fun v ↦ v * (1 + t v))
      (w • t' + (1 + t w) • ContinuousLinearMap.id ℝ (Fin n → ℝ)) s w := by
  convert (hasFDerivWithinAt_id w s).mul
    ((hasFDerivWithinAt_const (1 : Fin n → ℝ) w s).add ht) using 1 <;>
    ext <;> simp [mul_comm]







/-- Measurability of the Gamma determinant-moment integrand follows from
measurability of the displacement and determinant factor. -/
theorem measurable_gammaDeterminantIntegrand
    {n : ℕ} {α : ℝ}
    {t : (Fin n → ℝ) → (Fin n → ℝ)} {c : (Fin n → ℝ) → ℝ}
    (ht : Measurable t) (hc : Measurable c) :
    Measurable (fun w ↦ ENNReal.ofReal
      (c w * Real.exp (-α *
        (∑ i, (w i - 1) * t w i + ∑ i, (t w i) ^ 2)))) := by
  fun_prop











theorem gammaProduct_lintegral_le_one_of_ae_jacobian
    {n : ℕ} {α : ℝ} (hα : 0 < α)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s)
    {F : (Fin n → ℝ) → (Fin n → ℝ)}
    {F' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hF' : ∀ᵐ x ∂volume, x ∈ s → HasFDerivAt F (F' x) x)
    (hF : Set.InjOn F s) {Y : (Fin n → ℝ) → ENNReal}
    (hYmeas : Measurable Y)
    (hdom : ∀ᵐ x ∂volume, x ∈ s →
      gammaProductDensity n α α x * Y x ≤
        ENNReal.ofReal |(F' x).det| * gammaProductDensity n α α (F x)) :
    ∫⁻ x in s, Y x ∂gammaProductMeasure n α α ≤ 1 := by
  have hall : ∀ᵐ x ∂volume, x ∈ s →
      HasFDerivAt F (F' x) x ∧
        gammaProductDensity n α α x * Y x ≤
          ENNReal.ofReal |(F' x).det| * gammaProductDensity n α α (F x) := by
    filter_upwards [hF', hdom] with x hx hd hxs
    exact ⟨hx hxs, hd hxs⟩
  obtain ⟨d, hbad, hdmeas, hdnull⟩ := exists_measurable_superset_of_null (ae_iff.mp hall)
  have hgood : ∀ x ∈ s \ d,
      HasFDerivAt F (F' x) x ∧
        gammaProductDensity n α α x * Y x ≤
          ENNReal.ofReal |(F' x).det| * gammaProductDensity n α α (F x) := by
    intro x hx
    have hh : x ∈ s → HasFDerivAt F (F' x) x ∧
        gammaProductDensity n α α x * Y x ≤
          ENNReal.ofReal |(F' x).det| * gammaProductDensity n α α (F x) := by
      by_contra hn
      exact hx.2 (hbad hn)
    exact hh hx.1
  have hsd : s \ d =ᵐ[volume] s := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hdnull] with x hx
    exact propext ⟨fun h ↦ h.1, fun h ↦ ⟨h, hx⟩⟩
  have hsdGamma : s \ d =ᵐ[gammaProductMeasure n α α] s := by
    rw [gammaProductMeasure_eq_volume_withDensity]
    exact withDensity_absolutelyContinuous volume (gammaProductDensity n α α) hsd
  rw [← setLIntegral_congr hsdGamma]
  exact gammaProduct_lintegral_le_one_of_jacobian hα (hs.diff hdmeas)
    (fun x hx ↦ (hgood x hx).1.hasFDerivWithinAt)
    (hF.mono diff_subset) hYmeas (fun x hx ↦ (hgood x hx).2)



end ReweightedNPMLE
end

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
/-- The monotone Gamma change-of-variables theorem with only
almost-everywhere differentiability and Jacobian domination. -/
theorem solution
    {n : ℕ} {α : ℝ} (hα : 0 < α)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s)
    (t : (Fin n → ℝ) → (Fin n → ℝ)) (c : (Fin n → ℝ) → ℝ)
    (t' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (ht' : ∀ᵐ w ∂volume, w ∈ s → HasFDerivAt t (t' w) w)
    (htmeas : Measurable t) (hcmeas : Measurable c)
    (hw : ∀ w ∈ s, ∀ i, 0 < w i)
    (ht : ∀ w ∈ s, ∀ i, |t w i| ≤ 1 / 8)
    (hmono : ∀ w ∈ s, ∀ v ∈ s,
      0 ≤ ∑ i, (w i - v i) * (t w i - t v i))
    (hc : ∀ w ∈ s, 0 ≤ c w)
    (hdet : ∀ᵐ w ∂volume, w ∈ s →
      (∏ i, (1 + t w i)) * c w ≤
        |(w • t' w + (1 + t w) •
          ContinuousLinearMap.id ℝ (Fin n → ℝ)).det|) :
    ∫⁻ w in s, ENNReal.ofReal
        (c w * Real.exp (-α *
          (∑ i, (w i - 1) * t w i + ∑ i, (t w i) ^ 2)))
      ∂gammaProductMeasure n α α ≤ 1 := by
  let F := fun w ↦ w * (1 + t w)
  let F' := fun w ↦ w • t' w + (1 + t w) •
    ContinuousLinearMap.id ℝ (Fin n → ℝ)
  apply gammaProduct_lintegral_le_one_of_ae_jacobian hα hs (F := F) (F' := F')
  · filter_upwards [ht'] with w hw' hws
    exact (hasFDerivWithinAt_multiplicativeChange (s := univ)
      (hw' hws).hasFDerivWithinAt).hasFDerivAt_of_univ
  · apply multiplicativeChange_injOn_of_monotone t hw _ hmono
    intro w hws i
    have hi := neg_le_of_abs_le (ht w hws i)
    norm_num at hi ⊢
    linarith
  · exact measurable_gammaDeterminantIntegrand htmeas hcmeas
  · filter_upwards [hdet] with w hd hws
    exact gamma_density_jacobian_domination hα (hc w hws) (abs_nonneg _)
      w (t w) (hw w hws) (ht w hws) (hd hws)
