-- Prove2me | Definitions.Def_BenchmarkOperator20261026_RestrictedDensity
-- name    : BenchmarkOperator20261026_RestrictedDensity
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:38:23.285167+00:00
-- url     : https://prove2.me/theorems/5f223ec3-75aa-4174-b0a6-8bd5dd481beb
-- title:
--   Restricted Density
-- statement:
--   Defines the real exponential density, its weighted measure, the fixed base interval and the probability restriction to that interval. The retained normalization, density-shift and measure-class instances support finite products of these base measures.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization RestrictedDensity.lean, lines 14–81; source SHA-256 43c4658a790fda338610dec10e9d4b14db018903de5314d13bc1e0f169c5ae74. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

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

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace MeasureEquivalenceRestrictedProduct

def exponentialDensity (t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-t))
def exponentialMeasure : Measure ℝ := volume.withDensity exponentialDensity
def baseInterval : Set ℝ := Icc (-Real.log 2) 0
def baseMeasure : Measure ℝ := exponentialMeasure.restrict baseInterval

theorem measurable_exponentialDensity : Measurable exponentialDensity :=
  (Real.continuous_exp.comp continuous_neg).measurable.ennreal_ofReal

instance _root_.MeasureEquivalenceRestrictedProduct.instSigmaFiniteRealExponentialMeasure : SigmaFinite exponentialMeasure := by
  unfold exponentialMeasure exponentialDensity
  infer_instance

theorem exponentialMeasure_apply {s : Set ℝ} (hs : MeasurableSet s) :
    exponentialMeasure s = ∫⁻ t in s, exponentialDensity t :=
  withDensity_apply _ hs

theorem exponentialDensity_shift (a t : ℝ) :
    exponentialDensity (t - a) = ENNReal.ofReal (Real.exp a) * exponentialDensity t := by
  dsimp [exponentialDensity]
  rw [show -(t - a) = a + -t by ring, Real.exp_add,
    ENNReal.ofReal_mul (Real.exp_nonneg a)]

theorem map_add_exponentialMeasure (a : ℝ) :
    exponentialMeasure.map (fun t => t + a) =
      ENNReal.ofReal (Real.exp a) • exponentialMeasure := by
  have hm : Measurable (fun t : ℝ => t + a) := measurable_id.add_const a
  have hp : MeasurePreserving (fun t : ℝ => t + a) volume volume :=
    measurePreserving_add_right volume a
  ext s hs
  rw [Measure.map_apply hm hs, exponentialMeasure_apply (hm hs), Measure.smul_apply,
    exponentialMeasure_apply hs, smul_eq_mul]
  calc
    (∫⁻ t in (fun t : ℝ => t + a) ⁻¹' s, exponentialDensity t) =
        ∫⁻ t in (fun t : ℝ => t + a) ⁻¹' s, exponentialDensity ((t + a) - a) := by simp
    _ = ∫⁻ t in s, exponentialDensity (t - a) :=
      hp.setLIntegral_comp_preimage hs (measurable_exponentialDensity.comp (measurable_id.sub_const a))
    _ = ENNReal.ofReal (Real.exp a) * ∫⁻ t in s, exponentialDensity t := by
      simp_rw [exponentialDensity_shift]
      exact lintegral_const_mul _ measurable_exponentialDensity

theorem integral_baseInterval : (∫ t in baseInterval, Real.exp (-t)) = 1 := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [baseInterval, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (neg_nonpos.mpr hlog),
    intervalIntegral.integral_comp_neg, integral_exp]
  norm_num [Real.exp_log (by norm_num : (0 : ℝ) < 2)]

theorem exponentialMeasure_baseInterval : exponentialMeasure baseInterval = 1 := by
  rw [exponentialMeasure_apply (show MeasurableSet baseInterval from measurableSet_Icc)]
  dsimp only [exponentialDensity]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_baseInterval]
    norm_num
  · exact (Real.continuous_exp.comp continuous_neg).integrableOn_Icc
  · exact ae_of_all _ (fun t => Real.exp_nonneg _)

instance _root_.MeasureEquivalenceRestrictedProduct.instIsProbabilityMeasureRealBaseMeasure : IsProbabilityMeasure baseMeasure := by
  constructor
  rw [baseMeasure, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    exponentialMeasure_baseInterval]

instance _root_.MeasureEquivalenceRestrictedProduct.instNoAtomsRealExponentialMeasure : NoAtoms exponentialMeasure := by
  unfold exponentialMeasure
  infer_instance

instance _root_.MeasureEquivalenceRestrictedProduct.instNoAtomsRealBaseMeasure : NoAtoms baseMeasure := by
  unfold baseMeasure
  infer_instance







end MeasureEquivalenceRestrictedProduct


