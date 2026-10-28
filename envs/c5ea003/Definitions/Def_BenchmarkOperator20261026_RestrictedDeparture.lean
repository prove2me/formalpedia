-- Prove2me | Definitions.Def_BenchmarkOperator20261026_RestrictedDeparture
-- name    : BenchmarkOperator20261026_RestrictedDeparture
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:46:23.806857+00:00
-- url     : https://prove2.me/theorems/8fd83d6f-2cbf-448d-a568-6ef441b106e9
-- title:
--   Restricted Departure
-- statement:
--   Defines the event that a translated coordinate leaves the base interval and its base probability. The retained density and probability bounds estimate these departures. Later support theorems apply the bounds under summability hypotheses.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization RestrictedDeparture.lean, lines 11–78; source SHA-256 3dddc2281eae13725c9444a83e3caa08caf94aac59248efaca71afadf1a1d5f8. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_RestrictedDensity
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

def departureSet (u : ℝ) : Set ℝ := {t | t ∈ baseInterval ∧ t + u ∉ baseInterval}
def departureProbability (u : ℝ) : ℝ≥0∞ := baseMeasure (departureSet u)

theorem measurable_departureSet (u : ℝ) : MeasurableSet (departureSet u) :=
  (show MeasurableSet baseInterval from measurableSet_Icc).inter
    ((measurable_id.add_const u) (show MeasurableSet baseInterval from measurableSet_Icc)).compl

theorem exponentialDensity_le_two {t : ℝ} (ht : t ∈ baseInterval) :
    exponentialDensity t ≤ 2 := by
  have hle : Real.exp (-t) ≤ 2 := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.mpr (by linarith [ht.1])
  simpa [exponentialDensity] using ENNReal.ofReal_le_ofReal hle



theorem baseMeasure_le_two_volume : baseMeasure ≤ (2 : ℝ≥0∞) • (volume : Measure ℝ) := by
  have hle : baseMeasure ≤ (2 : ℝ≥0∞) • (volume.restrict baseInterval) := by
    unfold baseMeasure exponentialMeasure
    rw [restrict_withDensity (show MeasurableSet baseInterval from measurableSet_Icc)]
    rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem (show MeasurableSet baseInterval from measurableSet_Icc)] with t ht
    exact exponentialDensity_le_two ht
  apply hle.trans
  apply Measure.le_iff.mpr
  intro s hs
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_left' (Measure.restrict_le_self s) 2



theorem departureProbability_le (u : ℝ) :
    departureProbability u ≤ 2 * ENNReal.ofReal |u| := by
  have hρ := baseMeasure_le_two_volume (departureSet u)
  change departureProbability u ≤ _ at hρ
  simp only [Measure.smul_apply, smul_eq_mul] at hρ
  by_cases hu : 0 ≤ u
  · have hsub : departureSet u ⊆ Ioc (-u) 0 := by
      intro t ht
      have htl : -Real.log 2 ≤ t := ht.1.1
      have htr : t ≤ 0 := ht.1.2
      have hbad : ¬ (-Real.log 2 ≤ t + u ∧ t + u ≤ 0) := ht.2
      have hpos : 0 < t + u := by by_contra h; apply hbad; constructor <;> linarith
      constructor <;> linarith
    exact hρ.trans ((mul_le_mul_left' (measure_mono hsub) 2).trans_eq (by
      rw [Real.volume_Ioc]
      simp [abs_of_nonneg hu]))
  · have hu' : u ≤ 0 := le_of_not_ge hu
    have hsub : departureSet u ⊆ Ico (-Real.log 2) (-Real.log 2 - u) := by
      intro t ht
      have htl : -Real.log 2 ≤ t := ht.1.1
      have htr : t ≤ 0 := ht.1.2
      have hbad : ¬ (-Real.log 2 ≤ t + u ∧ t + u ≤ 0) := ht.2
      have hneg : t + u < -Real.log 2 := by by_contra h; apply hbad; constructor <;> linarith
      constructor <;> linarith
    exact hρ.trans ((mul_le_mul_left' (measure_mono hsub) 2).trans_eq (by
      rw [Real.volume_Ico]
      rw [show (-Real.log 2 - u) - -Real.log 2 = -u by ring, abs_of_nonpos hu']))











end MeasureEquivalenceRestrictedProduct


