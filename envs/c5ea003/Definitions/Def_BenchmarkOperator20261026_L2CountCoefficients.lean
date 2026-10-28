-- Prove2me | Definitions.Def_BenchmarkOperator20261026_L2CountCoefficients
-- name    : BenchmarkOperator20261026_L2CountCoefficients
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:33:10.697955+00:00
-- url     : https://prove2.me/theorems/ae39a639-de3a-4771-8232-f14f736356eb
-- title:
--   L2 Count Coefficients
-- statement:
--   Defines the bounded coordinate-coefficient maps from a product $L^2$ space with counting measure to the base $L^2$ space. The representative, boundedness and Parseval square-norm identities needed by these maps are retained. They provide the actual operator coefficients used in corner comparisons.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization L2CountCoefficients.lean, lines 20–100; source SHA-256 387bbdffb5883995693df01d57a94fe27134dc49d46457b8751fe39ad8db58a9. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_MeasureCantorTuple
import Definitions.Def_BenchmarkOperator20261026_MeasureUnitaryDensity
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

/-! Actual L2 coefficient operators in a counting-measure coordinate,
with their Fubini square-norm identity. -/

open MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal

namespace MeasureEquivalenceL2Coefficients

open MeasureUnitary

variable {X D : Type*} [MeasurableSpace X] [MeasurableSpace D]
    [Countable D] [MeasurableSingletonClass D]
    (μ : Measure X) [SigmaFinite μ]

omit [MeasurableSingletonClass D] in
theorem ae_slice_of_ae {f g : X × D → ℂ}
    (h : f =ᵐ[μ.prod (Measure.count : Measure D)] g) (d : D) :
    (fun x => f (x,d)) =ᵐ[μ] (fun x => g (x,d)) := by
  have hs := (Measure.measurePreserving_swap (μ := (Measure.count : Measure D)) (ν := μ)).quasiMeasurePreserving.ae_eq h
  have ha := Measure.ae_ae_of_ae_prod hs
  exact Measure.ae_count_iff.mp ha d

omit [MeasurableSingletonClass D] in
theorem coefficient_memLp (u : Lp ℂ 2 (μ.prod (Measure.count : Measure D))) (d : D) :
    MemLp (fun x => u (x,d)) 2 μ := by
  have hI : Integrable (fun p : X × D => ‖u p‖ ^ 2) (μ.prod Measure.count) :=
    (Lp.memLp u).norm.integrable_sq
  have hslice : Integrable (fun x => ‖u (x,d)‖ ^ 2) μ :=
    Measure.ae_count_iff.mp hI.prod_left_ae d
  apply (memLp_two_iff_integrable_sq_norm ?_).mpr hslice
  exact ((Lp.stronglyMeasurable u).comp_measurable
    (measurable_id.prodMk measurable_const)).aestronglyMeasurable

noncomputable def coefficient (d : D) (u : Lp ℂ 2 (μ.prod (Measure.count : Measure D))) : Lp ℂ 2 μ :=
  (coefficient_memLp μ u d).toLp (fun x => u (x,d))

omit [MeasurableSingletonClass D] in
theorem coefficient_coe (d : D) (u : Lp ℂ 2 (μ.prod (Measure.count : Measure D))) :
    coefficient μ d u =ᵐ[μ] (fun x => u (x,d)) :=
  (coefficient_memLp μ u d).coeFn_toLp

theorem coefficient_norm_sq (d : D) (u : Lp ℂ 2 (μ.prod (Measure.count : Measure D))) :
    ‖coefficient μ d u‖ ^ 2 = ∫ x, ‖u (x,d)‖ ^ 2 ∂μ := by
  rw [l2_norm_sq_integral]
  apply integral_congr_ae
  exact (coefficient_coe μ d u).mono (fun x hx => congrArg (fun z : ℂ => ‖z‖ ^ 2) hx)

theorem summable_coefficient_norm_sq (u : Lp ℂ 2 (μ.prod (Measure.count : Measure D))) :
    Summable (fun d => ‖coefficient μ d u‖ ^ 2) := by
  have hI : Integrable (fun p : X × D => ‖u p‖ ^ 2) (μ.prod Measure.count) :=
    (Lp.memLp u).norm.integrable_sq
  have hs := integrable_count_iff.mp hI.integral_prod_right
  simpa only [← coefficient_norm_sq, Real.norm_eq_abs, abs_sq] using hs

/-- Genuine Fubini/Parseval identity for the actual product L2 space. -/
theorem norm_sq_eq_tsum_coefficient_norm_sq
    (u : Lp ℂ 2 (μ.prod (Measure.count : Measure D))) :
    ‖u‖ ^ 2 = ∑' d, ‖coefficient μ d u‖ ^ 2 := by
  have hI : Integrable (fun p : X × D => ‖u p‖ ^ 2) (μ.prod Measure.count) :=
    (Lp.memLp u).norm.integrable_sq
  rw [l2_norm_sq_integral, integral_prod_symm _ hI,
    integral_countable hI.integral_prod_right]
  simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul,
    ← coefficient_norm_sq]

theorem coefficient_norm_le (d : D) (u : Lp ℂ 2 (μ.prod (Measure.count : Measure D))) :
    ‖coefficient μ d u‖ ≤ ‖u‖ := by
  have hsum := summable_coefficient_norm_sq μ u
  have hle : ‖coefficient μ d u‖ ^ 2 ≤ ∑' i, ‖coefficient μ i u‖ ^ 2 :=
    hsum.le_tsum d (fun _ _ => sq_nonneg _)
  rw [← norm_sq_eq_tsum_coefficient_norm_sq] at hle
  nlinarith [norm_nonneg (coefficient μ d u), norm_nonneg u]

noncomputable def coefficientCLM (d : D) :
    Lp ℂ 2 (μ.prod (Measure.count : Measure D)) →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := coefficient μ d
      map_add' := by
        intro u v
        apply Lp.ext
        filter_upwards [coefficient_coe μ d (u+v), coefficient_coe μ d u,
          coefficient_coe μ d v, Lp.coeFn_add (coefficient μ d u) (coefficient μ d v),
          ae_slice_of_ae μ (Lp.coeFn_add u v) d] with x huv hu hv hsum hsource
        simp only [Pi.add_apply] at hsum hsource
        rw [huv, hsum, hu, hv, hsource]
      map_smul' := by
        intro c u
        apply Lp.ext
        filter_upwards [coefficient_coe μ d (c • u), coefficient_coe μ d u,
          Lp.coeFn_smul c (coefficient μ d u), ae_slice_of_ae μ (Lp.coeFn_smul c u) d]
          with x hcu hu hsmul hsource
        simp only [Pi.smul_apply] at hsmul hsource
        simp only [RingHom.id_apply]
        rw [hcu, hsmul, hu, hsource] }
    1 (fun u => by simpa only [one_mul] using coefficient_norm_le μ d u)

end MeasureEquivalenceL2Coefficients


