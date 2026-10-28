-- Prove2me | solution 1 for MeasureEquivalenceZeroSumAffinity.uniform_coordinate_mean_affinity
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T13:28:59.1194+00:00
-- url     : https://prove2.me/submissions/861886ca-c155-4353-834a-3b366cecf68c

import Definitions.Def_BenchmarkOperator20261026_HellingerAffinity
import Definitions.Def_BenchmarkOperator20261026_HellingerInner
import Definitions.Def_BenchmarkOperator20261026_InvariantGraphGroup
import Definitions.Def_BenchmarkOperator20261026_RNGraph
import Definitions.Def_BenchmarkOperator20261026_RootContinuity
import Definitions.Def_BenchmarkOperator20261026_SolenoidGroups
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_MeasureEquivalenceHellinger_upperSemicontinuous_integrated_affinity_standardBorel
import Theorems.Thm_MeasureEquivalenceSolenoid_twoPoint_limit
import Theorems.Thm_MeasureEquivalenceZeroSumAffinity_uniform_twoPoint_affinity

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





























end
end MeasureEquivalenceSolenoid

end

/-! The actual compact-limit step in the quasi-invariance rigidity proof.
Upper semicontinuity of the averaged affinity transports uniform intrinsic
zero-sum estimates to a one-coordinate shift. -/
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped Topology ENNReal
namespace MeasureEquivalenceZeroSumAffinity
end MeasureEquivalenceZeroSumAffinity
open MeasureEquivalenceZeroSumAffinity
open MeasureEquivalenceSolenoid MeasureEquivalenceHellinger
  MeasureEquivalenceRNGraph MeasureEquivalenceRootContinuity
variable {Z : Type*} [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z]
    [BorelSpace Z]
    [MulAction (Multiplicative CompactSequences) Z]
    [ContinuousSMul (Multiplicative CompactSequences) Z]
    (M : Measure Z) [IsProbabilityMeasure M]
    (κ : Kernel Z Z) [IsMarkovKernel κ]
    (hQI : ∀ h : CompactSequences, h ∈ zeroSumSubgroup →
      Multiplicative.ofAdd h ∈ quasiInvariantSubgroup M)
    (hsplit : ∀ h : zeroSumSpace,
      affinity M (M.map (fun z => Multiplicative.ofAdd (zeroSumInclusion h) • z)) =
        ∫ x, affinity (κ x) ((κ x).map
          (fun z => Multiplicative.ofAdd (zeroSumInclusion h) • z)) ∂M)

include hQI hsplit

theorem solution (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : ℝ, |a| < δ →
      1 - ε ≤ ∫ x, affinity (κ x) ((κ x).map
        (fun z => Multiplicative.ofAdd (coordinateShift a) • z)) ∂M := by
  letI : Nonempty Z := nonempty_of_isProbabilityMeasure M
  letI : PolishSpace (Multiplicative CompactSequences) :=
    inferInstanceAs (PolishSpace CompactSequences)
  letI := upgradeIsCompletelyMetrizable (Multiplicative CompactSequences)
  obtain ⟨δ,hδ,hbound⟩ := uniform_twoPoint_affinity M hQI ε hε
  refine ⟨δ,hδ,?_⟩
  intro a ha
  let F : Multiplicative CompactSequences → ℝ := fun g =>
    ∫ x, affinity (κ x) ((κ x).map (fun z => g • z)) ∂M
  have hu : UpperSemicontinuous F :=
    upperSemicontinuous_integrated_affinity_standardBorel M κ
  have hclosed : IsClosed {g | 1-ε ≤ F g} := hu.isClosed_preimage (1-ε)
  have ht : Tendsto (fun n => Multiplicative.ofAdd (l1Embedding (twoPoint a n)))
      atTop (𝓝 (Multiplicative.ofAdd (coordinateShift a))) := twoPoint_limit a
  apply hclosed.mem_of_tendsto ht
  apply Eventually.of_forall
  intro n
  change 1-ε ≤ F (Multiplicative.ofAdd (l1Embedding (twoPoint a n)))
  have hs := hsplit ⟨twoPoint a n,twoPoint_zeroSum a n⟩
  change affinity M (M.map (fun z => Multiplicative.ofAdd
    (l1Embedding (twoPoint a n)) • z)) = F (Multiplicative.ofAdd
      (l1Embedding (twoPoint a n))) at hs
  rw [← hs]
  exact hbound a ha n
