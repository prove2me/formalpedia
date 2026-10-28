-- Prove2me | Definitions.Def_BenchmarkOperator20261026_L2CountInjections
-- name    : BenchmarkOperator20261026_L2CountInjections
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:33:50.261144+00:00
-- url     : https://prove2.me/theorems/18d95c73-8339-42c8-ab62-a678149f8caf
-- title:
--   L2 Count Injections
-- statement:
--   Defines the isometric insertion of a base $L^2$ vector into a single counting coordinate and the matrix coefficients of a bounded operator obtained from insertion and coefficient maps. The retained identities verify insertion norms, coordinate recovery and determination by all coefficients.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization L2CountInjections.lean, lines 17–135; source SHA-256 10cee485e4e6b3bb229ea187e1d112f48f5f144d315d8e1afa2a6d77849e10a7. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_L2CountCoefficients
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorTuple
import Mathlib.Data.Set.Lattice
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace MeasurableEquiv
end MeasurableEquiv
namespace MeasureEquivalenceCompactAveraging
end MeasureEquivalenceCompactAveraging
namespace MeasureEquivalenceDenseInvariance
end MeasureEquivalenceDenseInvariance
namespace MeasureEquivalenceDensity
end MeasureEquivalenceDensity
namespace MeasureEquivalenceDensityGraph
end MeasureEquivalenceDensityGraph
namespace MeasureEquivalenceEquidecomposition
end MeasureEquivalenceEquidecomposition
namespace MeasureEquivalenceEquidecomposition.greedyRemainder
end MeasureEquivalenceEquidecomposition.greedyRemainder
namespace MeasureEquivalenceErgodicDecomposition
end MeasureEquivalenceErgodicDecomposition
namespace MeasureEquivalenceHellinger
end MeasureEquivalenceHellinger
namespace MeasureEquivalenceInducedCorners
end MeasureEquivalenceInducedCorners
namespace MeasureEquivalenceInvariantGraph
end MeasureEquivalenceInvariantGraph
namespace MeasureEquivalenceInverseAC
end MeasureEquivalenceInverseAC
namespace MeasureEquivalenceL2Coefficients
end MeasureEquivalenceL2Coefficients
namespace MeasureEquivalenceL2Restriction
end MeasureEquivalenceL2Restriction
namespace MeasureEquivalenceL2Transport
end MeasureEquivalenceL2Transport
namespace MeasureEquivalenceMarkov
end MeasureEquivalenceMarkov
namespace MeasureEquivalenceMarkov.kernelIterate
end MeasureEquivalenceMarkov.kernelIterate
namespace MeasureEquivalenceRNGraph
end MeasureEquivalenceRNGraph
namespace MeasureEquivalenceRNPresentation
end MeasureEquivalenceRNPresentation
namespace MeasureEquivalenceResearch
end MeasureEquivalenceResearch
namespace MeasureEquivalenceRestrictedPhase
end MeasureEquivalenceRestrictedPhase
namespace MeasureEquivalenceRestrictedProduct
end MeasureEquivalenceRestrictedProduct
namespace MeasureEquivalenceRestrictedProduct.CompatibleStages
end MeasureEquivalenceRestrictedProduct.CompatibleStages
namespace MeasureEquivalenceRestrictedProduct.CompatibleStages.mk
end MeasureEquivalenceRestrictedProduct.CompatibleStages.mk
namespace MeasureEquivalenceRestrictedRoots
end MeasureEquivalenceRestrictedRoots
namespace MeasureEquivalenceRigidity
end MeasureEquivalenceRigidity
namespace MeasureEquivalenceRootContinuity
end MeasureEquivalenceRootContinuity
namespace MeasureEquivalenceSharedDensity
end MeasureEquivalenceSharedDensity
namespace MeasureEquivalenceSolenoid
end MeasureEquivalenceSolenoid
namespace MeasureEquivalenceTopology
end MeasureEquivalenceTopology
namespace MeasureEquivalenceZeroSumAffinity
end MeasureEquivalenceZeroSumAffinity
namespace MeasureUnitary
end MeasureUnitary
namespace MeasureUnitary.FiniteBorelSection
end MeasureUnitary.FiniteBorelSection
namespace OperatorCoding
end OperatorCoding
namespace OperatorCoding.operatorUnitaryPair
end OperatorCoding.operatorUnitaryPair
namespace lp
end lp

/-! Actual isometric coordinate injections into a product L2 space,
and coefficient matrices of actual bounded operators on these spaces. -/

open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal

namespace MeasureEquivalenceL2Coefficients

noncomputable section

variable {X D : Type*} [MeasurableSpace X] [MeasurableSpace D]
    [Countable D] [MeasurableSingletonClass D]
    (μ : Measure X) [SigmaFinite μ]

local instance _root_.MeasureEquivalenceL2Coefficients.instDecidableEq_l2CountInjections : DecidableEq D := Classical.decEq D

def injectionFun (d : D) (f : Lp ℂ 2 μ) (p : X × D) : ℂ :=
  if p.2 = d then f p.1 else 0

omit [SigmaFinite μ] in
theorem injectionFun_measurable (d : D) (f : Lp ℂ 2 μ) :
    Measurable (injectionFun μ d f) := by
  classical
  exact Measurable.ite
    (measurableSet_eq_fun (measurable_snd : Measurable (fun p : X × D => p.2))
      (measurable_const (a := d)))
    ((Lp.stronglyMeasurable f).measurable.comp measurable_fst) measurable_const

theorem injection_memLp (d : D) (f : Lp ℂ 2 μ) :
    MemLp (injectionFun μ d f) 2 (μ.prod (Measure.count : Measure D)) := by
  classical
  have hslice (x : X) : (fun i : D => ‖injectionFun μ d f (x,i)‖ ^ 2) =
      ({d} : Set D).indicator (fun _ => ‖f x‖ ^ 2) := by
    funext i
    by_cases hi : i = d <;> simp [injectionFun, hi]
  have hI (x : X) : Integrable (fun i : D => ‖injectionFun μ d f (x,i)‖ ^ 2)
      (Measure.count : Measure D) := by
    rw [hslice]
    exact (integrableOn_const (by simp : (Measure.count : Measure D) {d} ≠ ∞)).integrable_indicator
      (MeasurableSet.singleton d)
  have hval (x : X) : (∫ i : D, ‖injectionFun μ d f (x,i)‖ ^ 2 ∂Measure.count) = ‖f x‖ ^ 2 := by
    rw [hslice, integral_indicator_const (‖f x‖ ^ 2) (MeasurableSet.singleton d)]
    simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
  apply (memLp_two_iff_integrable_sq_norm (injectionFun_measurable μ d f).aestronglyMeasurable).mpr
  apply (integrable_prod_iff ((injectionFun_measurable μ d f).norm.pow_const 2).aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall hI, ?_⟩
  simpa only [Real.norm_eq_abs, abs_sq, hval] using (Lp.memLp f).norm.integrable_sq

def injection (d : D) (f : Lp ℂ 2 μ) : Lp ℂ 2 (μ.prod (Measure.count : Measure D)) :=
  (injection_memLp μ d f).toLp (injectionFun μ d f)

theorem injection_coe (d : D) (f : Lp ℂ 2 μ) :
    injection μ d f =ᵐ[μ.prod (Measure.count : Measure D)] injectionFun μ d f :=
  (injection_memLp μ d f).coeFn_toLp

theorem coefficient_injection (d e : D) (f : Lp ℂ 2 μ) :
    coefficient μ e (injection μ d f) = if e = d then f else 0 := by
  classical
  by_cases he : e = d
  · subst e
    rw [if_pos rfl]
    apply Lp.ext
    filter_upwards [coefficient_coe μ d (injection μ d f),
      ae_slice_of_ae μ (injection_coe μ d f) d] with x hc hi
    rw [hc, hi]
    simp [injectionFun]
  · rw [if_neg he]
    apply Lp.ext
    filter_upwards [coefficient_coe μ e (injection μ d f),
      ae_slice_of_ae μ (injection_coe μ d f) e, Lp.coeFn_zero ℂ 2 μ] with x hc hi hz
    rw [hc, hi, hz]
    simp only [injectionFun, if_neg he, Pi.zero_apply]

omit [MeasurableSingletonClass D] in
theorem coefficient_ext
    (u v : Lp ℂ 2 (μ.prod (Measure.count : Measure D)))
    (h : ∀ d, coefficient μ d u = coefficient μ d v) : u = v := by
  apply Lp.ext
  have hs (d : D) : (fun x => u (x,d)) =ᵐ[μ] (fun x => v (x,d)) := by
    have hu := coefficient_coe μ d u
    rw [h d] at hu
    exact hu.symm.trans (coefficient_coe μ d v)
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun (Lp.stronglyMeasurable u).measurable
      (Lp.stronglyMeasurable v).measurable)).mpr
  filter_upwards [ae_all_iff.mpr hs] with x hx
  exact Measure.ae_count_iff.mpr hx

theorem injection_norm (d : D) (f : Lp ℂ 2 μ) : ‖injection μ d f‖ = ‖f‖ := by
  classical
  have hsq : ‖injection μ d f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [norm_sq_eq_tsum_coefficient_norm_sq]
    trans ∑' e : D, if e = d then ‖f‖ ^ 2 else 0
    · apply tsum_congr
      intro e
      rw [coefficient_injection]
      by_cases he : e = d <;> simp [he]
    · simp
  nlinarith [norm_nonneg (injection μ d f), norm_nonneg f]

def injectionLI (d : D) : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 (μ.prod (Measure.count : Measure D)) where
  toFun := injection μ d
  map_add' := by
    intro f g
    apply coefficient_ext μ
    intro e
    change coefficient μ e (injection μ d (f+g)) =
      coefficientCLM μ e (injection μ d f + injection μ d g)
    rw [(coefficientCLM μ e).map_add]
    change coefficient μ e (injection μ d (f+g)) =
      coefficient μ e (injection μ d f) + coefficient μ e (injection μ d g)
    simp_rw [coefficient_injection]
    by_cases he : e = d <;> simp [he]
  map_smul' := by
    intro c f
    apply coefficient_ext μ
    intro e
    change coefficient μ e (injection μ d (c • f)) = coefficientCLM μ e (c • injection μ d f)
    rw [(coefficientCLM μ e).map_smul]
    change coefficient μ e (injection μ d (c • f)) = c • coefficient μ e (injection μ d f)
    simp_rw [coefficient_injection]
    by_cases he : e = d <;> simp [he]
  norm_map' := injection_norm μ d

variable {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [SigmaFinite ν]

/-- Genuine matrix coefficient, obtained by composing the actual
isometric input injection, bounded operator, and bounded output coefficient. -/
def matrixCoefficient
    (T : Lp ℂ 2 (μ.prod (Measure.count : Measure D)) →L[ℂ]
      Lp ℂ 2 (ν.prod (Measure.count : Measure D))) (d e : D) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν :=
  (coefficientCLM ν d).comp (T.comp (injectionLI μ e).toContinuousLinearMap)

end
end MeasureEquivalenceL2Coefficients


