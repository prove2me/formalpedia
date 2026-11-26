-- Prove2me | solution 1 for ReweightedNPMLE.finite_probability_optimizer_extreme_iff_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:01:12.102961+00:00
-- url     : https://prove2.me/submissions/eedc8958-0f26-4a3b-bdd6-0e1d62e62a9d

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fin.Embedding
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_augmented_linearIndepOn_iff_of_contact
import Theorems.Thm_ReweightedNPMLE_augmented_linearIndepOn_of_finiteMixtureFiber_extreme
import Theorems.Thm_ReweightedNPMLE_finiteMixtureFiber_extreme_of_augmented_linearIndepOn
import Theorems.Thm_ReweightedNPMLE_finiteProbabilityMeasure_extreme_of_linearIndependent
import Theorems.Thm_ReweightedNPMLE_isExtremeProbabilityMixture_iff
import Theorems.Thm_ReweightedNPMLE_likelihood_contact_on_finite_optimizer_support
import Theorems.Thm_ReweightedNPMLE_probabilityMixtureValue_finiteProbabilityMeasure

-- Inline helpers preserved from ReweightedNPMLE.FiniteOptimizerFiber.
section
/-!
# Extreme finite mixture fibers

This file isolates the finite-dimensional core of the paper's optimizer-fiber
lemma.  A probability vector represents a finite mixing law.  If the
dictionary vectors indexed by its nonzero masses are linearly independent,
then that representation is an extreme point of the fiber of all probability
vectors with the same fitted value.
-/

open Set
open scoped BigOperators

namespace ReweightedNPMLE























@[simp] theorem mem_coefficientSupport {m : ℕ} (p : Fin m → ℝ) (i : Fin m) :
    i ∈ coefficientSupport p ↔ p i ≠ 0 := by
  simp [coefficientSupport]













/-- Characterization of the extreme points of a finite mixture fiber. -/
theorem finiteMixtureFiber_extreme_iff_augmented_linearIndepOn
    {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Fin m → E) (v : E) (p : Fin m → ℝ) :
    p ∈ (finiteMixtureFiber A v).extremePoints ℝ ↔
      p ∈ finiteMixtureFiber A v ∧
        LinearIndepOn ℝ (augmentedDictionary A)
          (coefficientSupport p : Set (Fin m)) := by
  constructor
  · intro hp
    exact ⟨hp.1, augmented_linearIndepOn_of_finiteMixtureFiber_extreme A v p hp⟩
  · rintro ⟨hp, hlin⟩
    exact finiteMixtureFiber_extreme_of_augmented_linearIndepOn A v p hp hlin





/-- With a contact functional, the paper's stated linear-independence
characterization of an extreme optimizer is exact. -/
theorem finiteMixtureFiber_extreme_iff_linearIndepOn_of_contact
    {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : Fin m → E) (v : E) (p : Fin m → ℝ) (b : E →ₗ[ℝ] ℝ)
    (hcontact : ∀ i ∈ coefficientSupport p, b (A i) = 1) :
    p ∈ (finiteMixtureFiber A v).extremePoints ℝ ↔
      p ∈ finiteMixtureFiber A v ∧
        LinearIndepOn ℝ A (coefficientSupport p : Set (Fin m)) := by
  rw [finiteMixtureFiber_extreme_iff_augmented_linearIndepOn]
  exact and_congr_right fun _ ↦
    augmented_linearIndepOn_iff_of_contact A (coefficientSupport p) b hcontact







end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.FittedContact.
section
/-!
# Likelihood contact hyperplanes

At a positive fitted-value maximizer, differentiating toward any other
feasible fitted vector gives the supporting hyperplane used in the paper's
extreme-optimizer argument.  This file proves that first-order statement and
packages its normalized linear functional.
-/

open Set
open scoped BigOperators

namespace ReweightedNPMLE




  










/-- Exact finite-dictionary form of the paper's extreme-optimizer lemma:
under positive likelihood weights, an optimizing probability vector is
extreme precisely when its active evaluation vectors are linearly
independent. -/
theorem finite_likelihood_optimizer_extreme_iff_linearIndepOn
    {m n : ℕ} [Nonempty (Fin n)]
    (A : Fin m → Fin n → ℝ) (v : Fin n → ℝ) (p : Fin m → ℝ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hp : p ∈ finiteMixtureFiber A v) (hvpos : ∀ i, 0 < v i)
    (hApos : ∀ j i, 0 < A j i)
    (hvmax : IsMaxOn (convexHull ℝ (Set.range A))
      (weightedLogLikelihood w) v) :
    p ∈ (finiteMixtureFiber A v).extremePoints ℝ ↔
      LinearIndepOn ℝ A (coefficientSupport p : Set (Fin m)) := by
  have hcontact := likelihood_contact_on_finite_optimizer_support
    A v p w hw hp hvpos hApos hvmax
  rw [finiteMixtureFiber_extreme_iff_linearIndepOn_of_contact
    A v p (likelihoodContactFunctional w v) hcontact, and_iff_right hp]



end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.ProbabilityFiberGeometry.
section
/-!
# Real-vector-space geometry of full probability fibers

Integration against continuous test functions embeds probability measures
injectively into a locally convex real vector space with its product topology.
The weakly compact mixture fiber has a compact convex image. Extreme points
are thus mathlib extreme points of a faithful representation of the full
probability-measure fiber, rather than of a finite coefficient simplex.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

namespace ReweightedNPMLE





theorem probabilityIntegralFunctional_injective {Θ : Type*}
    [TopologicalSpace Θ] [HasOuterApproxClosed Θ] [MeasurableSpace Θ] [BorelSpace Θ] :
    Function.Injective (probabilityIntegralFunctional (Θ := Θ)) := by
  intro μ ν h
  have hh : μ.toFiniteMeasure = ν.toFiniteMeasure :=
    FiniteMeasure.ext_of_forall_integral_eq (fun f ↦ congrFun h f.toContinuousMap)
  apply ProbabilityMeasure.toMeasure_injective
  exact congrArg (fun ρ : FiniteMeasure Θ ↦ (ρ : Measure Θ)) hh

theorem probabilityIntegralFunctional_convexCombination {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    (a b : ℝ≥0) (hab : a + b = 1) (μ ν : ProbabilityMeasure Θ) :
    probabilityIntegralFunctional (probabilityConvexCombination a b hab μ ν) =
      (a : ℝ) • probabilityIntegralFunctional μ + (b : ℝ) • probabilityIntegralFunctional ν := by
  funext f
  have hμ := f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
    (μ := (μ : Measure Θ))
  have hν := f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
    (μ := (ν : Measure Θ))
  change (∫ θ, f θ ∂(a • (μ : Measure Θ) + b • (ν : Measure Θ))) = _
  rw [integral_add_measure hμ.smul_measure_nnreal hν.smul_measure_nnreal]
  simp only [integral_smul_nnreal_measure, probabilityIntegralFunctional, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  rfl



















end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.FiniteProbabilityExtreme.
section
/-!
# Independent finite mixing laws are full-fiber extreme points

Finite-support representation and uniqueness are proved for arbitrary
probability measures concentrated on that finite support. Consequently,
an independent finite mixing law is extreme against decompositions into
arbitrary probability measures, not only against finite coefficient vectors.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

namespace ReweightedNPMLE







theorem finiteProbabilityMeasure_singleton_mass {Θ : Type*}
    [MeasurableSpace Θ] [MeasurableSingletonClass Θ] {m : ℕ}
    (θ : Fin m → Θ) (hθ : Function.Injective θ)
    (p : Fin m → ℝ) (hp : p ∈ finiteSimplex m) (j : Fin m) :
    (finiteProbabilityMeasure θ p hp : Measure Θ) {θ j} = ENNReal.ofReal (p j) := by
  classical
  change (∑ k, ENNReal.ofReal (p k) • Measure.dirac (θ k)) {θ j} = _
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    have hneq : θ k ≠ θ j := fun hh ↦ hkj (hθ hh)
    simp [hneq]
  · simp

theorem finiteProbabilityMeasure_coefficients_injective {Θ : Type*}
    [MeasurableSpace Θ] [MeasurableSingletonClass Θ] {m : ℕ}
    (θ : Fin m → Θ) (hθ : Function.Injective θ)
    (p q : Fin m → ℝ) (hp : p ∈ finiteSimplex m) (hq : q ∈ finiteSimplex m)
    (heq : finiteProbabilityMeasure θ p hp = finiteProbabilityMeasure θ q hq) : p = q := by
  funext j
  have hh := congrArg (fun μ : ProbabilityMeasure Θ ↦ (μ : Measure Θ) {θ j}) heq
  dsimp only at hh
  rw [finiteProbabilityMeasure_singleton_mass θ hθ p hp,
    finiteProbabilityMeasure_singleton_mass θ hθ q hq] at hh
  have hr := congrArg ENNReal.toReal hh
  simpa only [ENNReal.toReal_ofReal (hp.1 j), ENNReal.toReal_ofReal (hq.1 j)] using hr



theorem probabilityIntegralFunctional_finiteProbabilityMeasure {Θ : Type*}
    [TopologicalSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]
    {m : ℕ} (θ : Fin m → Θ) (p : Fin m → ℝ) (hp : p ∈ finiteSimplex m) (f : C(Θ, ℝ)) :
    probabilityIntegralFunctional (finiteProbabilityMeasure θ p hp) f = ∑ j, p j * f (θ j) := by
  have hh := congrFun (probabilityMixtureValue_finiteProbabilityMeasure
    (fun x : Θ ↦ fun _ : Fin 1 ↦ f x) (by fun_prop) θ p hp) (0 : Fin 1)
  simpa only [probabilityMixtureValue, probabilityIntegralFunctional, finiteMixtureValue,
    Function.comp_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hh

theorem finiteProbabilityMeasure_convexCombination {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {m : ℕ} (θ : Fin m → Θ) (p q r : Fin m → ℝ)
    (hp : p ∈ finiteSimplex m) (hq : q ∈ finiteSimplex m) (hr : r ∈ finiteSimplex m)
    (a b : ℝ≥0) (hab : a + b = 1)
    (hrepr : (a : ℝ) • q + (b : ℝ) • r = p) :
    probabilityConvexCombination a b hab (finiteProbabilityMeasure θ q hq)
      (finiteProbabilityMeasure θ r hr) = finiteProbabilityMeasure θ p hp := by
  apply probabilityIntegralFunctional_injective
  rw [probabilityIntegralFunctional_convexCombination]
  funext f
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    probabilityIntegralFunctional_finiteProbabilityMeasure, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hj := congrFun hrepr j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hj
  rw [← hj]
  ring







theorem finiteMixtureFiber_extreme_of_probability_extreme {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {m n : ℕ} (A : Θ → Fin n → ℝ) (hA : Continuous A)
    (θ : Fin m → Θ) (hθ : Function.Injective θ) (v : Fin n → ℝ)
    (p : Fin m → ℝ) (hp : p ∈ finiteMixtureFiber (A ∘ θ) v)
    (hext : IsExtremeProbabilityMixture A v (finiteProbabilityMeasure θ p hp.1)) :
    p ∈ (finiteMixtureFiber (A ∘ θ) v).extremePoints ℝ := by
  rw [mem_extremePoints_iff_left]
  refine ⟨hp, ?_⟩
  rintro q hq r hr ⟨a, b, ha, hb, hab, hrepr⟩
  let a' : ℝ≥0 := ⟨a, ha.le⟩
  let b' : ℝ≥0 := ⟨b, hb.le⟩
  have hab' : a' + b' = 1 := by apply Subtype.ext; exact hab
  have hqval : finiteProbabilityMeasure θ q hq.1 ∈ probabilityMixtureFiber A v := by
    change probabilityMixtureValue A (finiteProbabilityMeasure θ q hq.1) = v
    rw [probabilityMixtureValue_finiteProbabilityMeasure A hA θ q hq.1]
    exact hq.2
  have hrval : finiteProbabilityMeasure θ r hr.1 ∈ probabilityMixtureFiber A v := by
    change probabilityMixtureValue A (finiteProbabilityMeasure θ r hr.1) = v
    rw [probabilityMixtureValue_finiteProbabilityMeasure A hA θ r hr.1]
    exact hr.2
  have heq := (isExtremeProbabilityMixture_iff A v _).mp hext |>.2
    a' b' (by exact_mod_cast ha) (by exact_mod_cast hb) hab'
    (finiteProbabilityMeasure θ q hq.1) (finiteProbabilityMeasure θ r hr.1) hqval hrval
    (finiteProbabilityMeasure_convexCombination θ p q r hp.1 hq.1 hr.1 a' b' hab' hrepr)
  exact finiteProbabilityMeasure_coefficients_injective θ hθ q p hq.1 hp.1 heq



end ReweightedNPMLE
end

/-!
# Independent finite mixing laws are full-fiber extreme points

Finite-support representation and uniqueness are proved for arbitrary
probability measures concentrated on that finite support. Consequently,
an independent finite mixing law is extreme against decompositions into
arbitrary probability measures, not only against finite coefficient vectors.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution {Θ : Type*}
    [MetricSpace Θ] [CompactSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ]
    {m n : ℕ} [Nonempty (Fin n)] (A : Θ → Fin n → ℝ) (hA : Continuous A)
    (θ : Fin m → Θ) (hθ : Function.Injective θ) (v : Fin n → ℝ)
    (p : Fin m → ℝ) (hp : p ∈ finiteMixtureFiber (A ∘ θ) v) (hpPos : ∀ j, 0 < p j)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (hvpos : ∀ i, 0 < v i)
    (hApos : ∀ j i, 0 < A (θ j) i)
    (hvmax : IsMaxOn (convexHull ℝ (range (A ∘ θ))) (weightedLogLikelihood w) v) :
    IsExtremeProbabilityMixture A v (finiteProbabilityMeasure θ p hp.1) ↔
      LinearIndependent ℝ (A ∘ θ) := by
  constructor
  · intro hext
    have hf := finiteMixtureFiber_extreme_of_probability_extreme A hA θ hθ v p hp hext
    have hl := (finite_likelihood_optimizer_extreme_iff_linearIndepOn
      (A ∘ θ) v p w hw hp hvpos hApos hvmax).mp hf
    have hs : (coefficientSupport p : Set (Fin m)) = univ := by
      ext j
      simp only [Finset.mem_coe, mem_coefficientSupport, mem_univ, iff_true]
      exact (hpPos j).ne'
    rw [hs, linearIndepOn_univ_iff] at hl
    exact hl
  · intro hl
    simpa only [hp.2] using finiteProbabilityMeasure_extreme_of_linearIndependent A hA θ p hp.1 hl
