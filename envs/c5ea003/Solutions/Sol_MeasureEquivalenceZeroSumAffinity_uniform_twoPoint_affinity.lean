-- Prove2me | solution 1 for MeasureEquivalenceZeroSumAffinity.uniform_twoPoint_affinity
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T13:25:27.04562+00:00
-- url     : https://prove2.me/submissions/749350c5-07b3-48e8-b6f3-de3fa1c5d91b

import Definitions.Def_BenchmarkOperator20261026_HellingerAffinity
import Definitions.Def_BenchmarkOperator20261026_HellingerInner
import Definitions.Def_BenchmarkOperator20261026_HellingerTransport
import Definitions.Def_BenchmarkOperator20261026_InvariantGraphGroup
import Definitions.Def_BenchmarkOperator20261026_RNGraph
import Definitions.Def_BenchmarkOperator20261026_RootContinuity
import Definitions.Def_BenchmarkOperator20261026_SolenoidGroups
import Definitions.Def_BenchmarkOperator20261026_ZeroSumAffinity
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.MetricSpace.Polish
import Theorems.Thm_MeasureEquivalenceRootContinuity_zeroSumRoot_continuous

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

-- Preserved source skeleton: SolenoidGroups
section
/-! The compact solenoid group and its real-sequence embedding from Section 8.
This file contains supporting lemmas, not the operator separation theorem. -/

open Filter Topology TopologicalSpace
open scoped Topology ENNReal

namespace MeasureEquivalenceSolenoid

noncomputable section

































































theorem twoPoint_zeroSum (a : ℝ) (n : ℕ) : twoPoint a n ∈ zeroSumSpace := by
  change (lp.tsumCLM ℝ ℕ ℝ) (twoPoint a n) = 0
  rw [twoPoint, map_sub]
  simp [lp.tsumCLM_apply]

theorem twoPoint_norm_le (a : ℝ) (n : ℕ) : ‖twoPoint a n‖ ≤ 2 * |a| := by
  calc
    ‖twoPoint a n‖ ≤ ‖(lp.single 1 0 a : RealL1)‖ + ‖(lp.single 1 (n+1) a : RealL1)‖ := norm_sub_le _ _
    _ = 2 * |a| := by simp [lp.norm_single]; ring



























end
end MeasureEquivalenceSolenoid

end

-- Preserved source skeleton: ZeroSumAffinity
section
/-! The uniform small-shift affinity estimate for the intrinsic zero-sum
l1 subgroup, derived from actual RN roots rather than assumed. -/

open MeasureTheory Filter Topology
open scoped Topology ENNReal

noncomputable section

namespace MeasureEquivalenceZeroSumAffinity

open MeasureEquivalenceSolenoid MeasureEquivalenceRootContinuity
open MeasureEquivalenceRNGraph MeasureEquivalenceHellinger

variable {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]
    [MulAction (Multiplicative CompactSequences) Z]
    [ContinuousSMul (Multiplicative CompactSequences) Z]
    (M : Measure Z) [IsProbabilityMeasure M]
    (hQI : ∀ h : CompactSequences, h ∈ zeroSumSubgroup →
      Multiplicative.ofAdd h ∈ quasiInvariantSubgroup M)



include hQI in
theorem zeroSumAffinity_continuous : Continuous (zeroSumAffinity M) := by
  have he : zeroSumAffinity M = fun h : zeroSumSpace =>
      inner ℝ (root M M) (zeroSumRoot M h) := by
    funext h
    exact affinity_eq_inner_roots M _ M Measure.AbsolutelyContinuous.rfl
      (hQI _ ⟨h, h.property, rfl⟩).1
  rw [he]
  exact continuous_const.inner (zeroSumRoot_continuous M hQI)

theorem zeroSumAffinity_zero : zeroSumAffinity M 0 = 1 := by
  change affinity M (M.map (fun z => Multiplicative.ofAdd (zeroSumInclusion 0) • z)) = 1
  have hz : zeroSumInclusion 0 = 0 := map_zero zeroSumInclusion
  rw [hz]
  change affinity M (M.map (fun z => (1 : Multiplicative CompactSequences) • z)) = 1
  simpa only [one_smul, Measure.map_id'] using affinity_self M



end MeasureEquivalenceZeroSumAffinity

end

/-! The uniform small-shift affinity estimate for the intrinsic zero-sum
l1 subgroup, derived from actual RN roots rather than assumed. -/
open MeasureTheory Filter Topology
open scoped Topology ENNReal
namespace MeasureEquivalenceZeroSumAffinity
end MeasureEquivalenceZeroSumAffinity
open MeasureEquivalenceZeroSumAffinity
open MeasureEquivalenceSolenoid MeasureEquivalenceRootContinuity
open MeasureEquivalenceRNGraph MeasureEquivalenceHellinger
variable {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]
    [MulAction (Multiplicative CompactSequences) Z]
    [ContinuousSMul (Multiplicative CompactSequences) Z]
    (M : Measure Z) [IsProbabilityMeasure M]
    (hQI : ∀ h : CompactSequences, h ∈ zeroSumSubgroup →
      Multiplicative.ofAdd h ∈ quasiInvariantSubgroup M)

include hQI

theorem solution (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : ℝ, |a| < δ → ∀ n : ℕ,
      1 - ε ≤ affinity M
        (M.map (fun z => Multiplicative.ofAdd (l1Embedding (twoPoint a n)) • z)) := by
  have hzero := zeroSumAffinity_zero M
  have hev : ∀ᶠ h : zeroSumSpace in 𝓝 0, 1 - ε < zeroSumAffinity M h :=
    (zeroSumAffinity_continuous M hQI).continuousAt.eventually
      (lt_mem_nhds (by rw [hzero]; linarith : 1-ε < zeroSumAffinity M 0))
  obtain ⟨d, hd, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨d/2, by positivity, ?_⟩
  intro a ha n
  let u : zeroSumSpace := ⟨twoPoint a n, twoPoint_zeroSum a n⟩
  have hu : dist u 0 < d := by
    rw [dist_zero_right]
    change ‖twoPoint a n‖ < d
    exact (twoPoint_norm_le a n).trans_lt (by linarith)
  exact (hball hu).le
