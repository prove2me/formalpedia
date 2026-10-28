-- Prove2me | solution 1 for MeasureEquivalenceRigidity.coordinateShift_quasiInvariant
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T13:32:31.326341+00:00
-- url     : https://prove2.me/submissions/fa7da6e3-d160-4437-835d-bdd2d8d58e0f

import Definitions.Def_BenchmarkOperator20261026_HellingerAffinity
import Definitions.Def_BenchmarkOperator20261026_HellingerInner
import Definitions.Def_BenchmarkOperator20261026_InvariantConditional
import Definitions.Def_BenchmarkOperator20261026_InvariantGraphGroup
import Definitions.Def_BenchmarkOperator20261026_MetropolisCoupling
import Definitions.Def_BenchmarkOperator20261026_OrbitMarkov
import Definitions.Def_BenchmarkOperator20261026_RNGraph
import Definitions.Def_BenchmarkOperator20261026_RootContinuity
import Definitions.Def_BenchmarkOperator20261026_SolenoidGroups
import Definitions.Def_BenchmarkOperator20261026_ZeroSumConditional
import Definitions.Def_BenchmarkOperator20261026_ZeroSumDense
import Definitions.Def_BenchmarkOperator20261026_ZeroSumRigidity
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.Disintegration.Unique
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_MeasureEquivalenceDenseInvariance_ae_invariant_of_dense
import Theorems.Thm_MeasureEquivalenceErgodicDecomposition_invariantConditionalKernel_affinity
import Theorems.Thm_MeasureEquivalenceRigidity_quasiInvariant_of_uniform_invariant_mean_affinity
import Theorems.Thm_MeasureEquivalenceZeroSumAffinity_uniform_coordinate_mean_affinity

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












































theorem l1Embedding_continuous : Continuous l1Embedding := by
  apply sequenceEmbedding_continuous.comp
  apply continuous_pi
  intro n
  exact (lp.lipschitzWith_one_eval (E := fun _ : ℕ => ℝ) (1:ℝ≥0∞) n).continuous


















































end
end MeasureEquivalenceSolenoid

end

-- Preserved source skeleton: RootContinuity
section
/-! Actual Radon--Nikodym root continuity for the zero-sum l1 subgroup.
The general closed-graph argument is reused from the archived sequence-space
development. No continuity of densities is assumed. -/

open MeasureTheory Set TopologicalSpace
open scoped Topology ENNReal

noncomputable section

namespace MeasureEquivalenceRootContinuity

open MeasureEquivalenceDensity MeasureEquivalenceHellinger
open MeasureEquivalenceRNGraph MeasureEquivalenceInvariantGraph

section General

variable {A Z G : Type*}
    [CommGroup A] [MetricSpace A] [IsTopologicalGroup A]
    [CompleteSpace A] [SecondCountableTopology A]
    [MeasurableSpace Z] [TopologicalSpace Z] [PolishSpace Z] [BorelSpace Z]
    [MulAction A Z] [ContinuousSMul A Z]
    (M : Measure Z) [IsProbabilityMeasure M]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G]



end General

open MeasureEquivalenceSolenoid



theorem zeroSumInclusion_continuous : Continuous zeroSumInclusion :=
  l1Embedding_continuous.comp continuous_subtype_val

section ActualAction

variable {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]
    [MulAction (Multiplicative CompactSequences) Z]
    [ContinuousSMul (Multiplicative CompactSequences) Z]
    (M : Measure Z) [IsProbabilityMeasure M]





end ActualAction

end MeasureEquivalenceRootContinuity

end

-- Preserved source skeleton: ZeroSumDense
section
/-! A countable dense subgroup of the intrinsic zero-sum l1 group. -/

open Filter Topology TopologicalSpace Set
open scoped Topology ENNReal

namespace MeasureEquivalenceSolenoid

noncomputable section





theorem rationalFinite_dense : DenseRange rationalFinite := by
  let R := rationalFinite.range
  have hs (i : ℕ) (a : ℝ) : lp.single 1 i a ∈ R.topologicalClosure := by
    have ha : a ∈ closure (range (fun q : ℚ => (q:ℝ))) := Rat.denseRange_cast a
    have hi : Continuous (fun a : ℝ => (lp.single 1 i a : RealL1)) :=
      (lp.singleContinuousAddMonoidHom (fun _ : ℕ => ℝ) 1 i).continuous
    have hm := mem_closure_image (hi.continuousAt : ContinuousAt
      (fun a : ℝ => (lp.single 1 i a : RealL1)) a) ha
    apply closure_mono (s := (fun a : ℝ => (lp.single 1 i a : RealL1)) ''
      range (fun q : ℚ => (q:ℝ))) (t := (R:Set RealL1)) _ hm
    rintro _ ⟨a, ⟨q, rfl⟩, rfl⟩
    exact ⟨Finsupp.single i q, rationalFinite_single i q⟩
  intro x
  change x ∈ R.topologicalClosure
  apply R.isClosed_topologicalClosure.mem_of_tendsto
    (lp.hasSum_single (by norm_num : (1:ℝ≥0∞) ≠ ⊤) x)
  exact Filter.Eventually.of_forall (fun s =>
    R.topologicalClosure.sum_mem (fun i _hi => hs i (x i)))



theorem zeroSumProjection_continuous : Continuous zeroSumProjection := by
  apply Continuous.subtype_mk
  exact continuous_id.sub
    ((lp.singleContinuousAddMonoidHom (fun _ : ℕ => ℝ) 1 0).continuous.comp
      (lp.tsumCLM ℝ ℕ ℝ).continuous)

theorem zeroSumProjection_surjective : Function.Surjective zeroSumProjection := by
  intro h
  refine ⟨h, Subtype.ext ?_⟩
  have hh : (lp.tsumCLM ℝ ℕ ℝ) (h:RealL1) = 0 := h.property
  change (h:RealL1) - lp.single 1 0 ((lp.tsumCLM ℝ ℕ ℝ) (h:RealL1)) = (h:RealL1)
  rw [hh]
  simp



theorem rationalZeroSum_dense : DenseRange rationalZeroSum :=
  zeroSumProjection_surjective.denseRange.comp rationalFinite_dense zeroSumProjection_continuous





theorem denseRationalSubgroup_dense : Dense (denseRationalSubgroup:Set zeroSumSpace) :=
  rationalZeroSum_dense



end
end MeasureEquivalenceSolenoid

end

-- Preserved source skeleton: DenseInvariantAffinity
section
/-! The true affinity formula for every element of an intrinsic Polish
group, after conditioning on a dense subgroup's invariant sigma algebra. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace MeasureEquivalenceDenseInvariance

open MeasureEquivalenceDensity MeasureEquivalenceRNGraph
  MeasureEquivalenceErgodicDecomposition MeasureEquivalenceHellinger

variable {A Z G : Type*}
    [CommGroup A] [MetricSpace A] [IsTopologicalGroup A]
    [CompleteSpace A] [SecondCountableTopology A]
    [MeasurableSpace Z] [TopologicalSpace Z] [PolishSpace Z] [BorelSpace Z]
    [MulAction A Z] [ContinuousSMul A Z]
    (M : Measure Z) [IsProbabilityMeasure M]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (i : G →* A) (hi : Continuous i)
    (hmem : ∀ g, i g ∈ quasiInvariantSubgroup (K := A) M)
    (D : Subgroup G) (hD : Dense (D : Set G))

include hi hmem hD in
theorem denseInvariant_affinity (g : G) :
    letI : MulAction D Z := MulAction.compHom Z (i.comp D.subtype)
    affinity M (M.map (fun z => i g • z)) =
      ∫ x, affinity (invariantConditionalKernel (G := D) M x)
        ((invariantConditionalKernel (G := D) M x).map (fun z => i g • z)) ∂M := by
  letI : MulAction D Z := MulAction.compHom Z (i.comp D.subtype)
  apply invariantConditionalKernel_affinity M (MeasurableEquiv.smul (i g))
  intro s hs
  apply ae_invariant_of_dense M i hi hmem (D : Set G) hD s hs.1 _ g
  intro d hd
  apply EventuallyEq.of_eq
  exact hs.2 ⟨d,hd⟩

end MeasureEquivalenceDenseInvariance

end

-- Preserved source skeleton: ZeroSumConditional
section
/-! The actual dense rational zero-sum conditional kernel and its
unconditional affinity disintegration for all intrinsic zero-sum shifts. -/

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped ENNReal

namespace MeasureEquivalenceRigidity

noncomputable section

open MeasureEquivalenceSolenoid MeasureEquivalenceRootContinuity
  MeasureEquivalenceRNGraph MeasureEquivalenceHellinger
  MeasureEquivalenceErgodicDecomposition MeasureEquivalenceDenseInvariance





theorem rationalZeroSumGroup_dense : Dense (rationalZeroSumGroup : Set
    (Multiplicative zeroSumSpace)) := denseRationalSubgroup_dense



variable {Z : Type*} [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z]
    [BorelSpace Z]
    [MulAction (Multiplicative CompactSequences) Z]
    [ContinuousSMul (Multiplicative CompactSequences) Z]







variable (M : Measure Z) [IsProbabilityMeasure M]
    (hQI : ∀ h : CompactSequences, h ∈ zeroSumSubgroup →
      Multiplicative.ofAdd h ∈ quasiInvariantSubgroup M)

include hQI in
theorem zeroSumComponentKernel_affinity (h : zeroSumSpace) :
    affinity M (M.map (fun z => Multiplicative.ofAdd (zeroSumInclusion h) • z)) =
      ∫ x, affinity (zeroSumComponentKernel M x) ((zeroSumComponentKernel M x).map
        (fun z => Multiplicative.ofAdd (zeroSumInclusion h) • z)) ∂M := by
  letI : PolishSpace (Multiplicative CompactSequences) :=
    inferInstanceAs (PolishSpace CompactSequences)
  letI := upgradeIsCompletelyMetrizable (Multiplicative CompactSequences)
  letI : PolishSpace (Multiplicative zeroSumSpace) :=
    inferInstanceAs (PolishSpace zeroSumSpace)
  letI : MeasurableSpace (Multiplicative zeroSumSpace) := borel (Multiplicative zeroSumSpace)
  letI : BorelSpace (Multiplicative zeroSumSpace) := ⟨rfl⟩
  have hi : Continuous zeroSumGroupHom := zeroSumInclusion_continuous
  have hm (g : Multiplicative zeroSumSpace) :
      zeroSumGroupHom g ∈ quasiInvariantSubgroup M :=
    hQI _ ⟨g.toAdd,g.toAdd.property,rfl⟩
  exact denseInvariant_affinity M zeroSumGroupHom hi hm rationalZeroSumGroup
    rationalZeroSumGroup_dense (Multiplicative.ofAdd h)

include hQI in
theorem zeroSumComponentKernel_coordinate_mean (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : ℝ, |a| < δ →
      1-ε ≤ ∫ x, affinity (zeroSumComponentKernel M x)
        ((zeroSumComponentKernel M x).map
          (fun z => Multiplicative.ofAdd (coordinateShift a) • z)) ∂M :=
  MeasureEquivalenceZeroSumAffinity.uniform_coordinate_mean_affinity M
    (zeroSumComponentKernel M) hQI (zeroSumComponentKernel_affinity M hQI) ε hε

end
end MeasureEquivalenceRigidity

end

/-! Actual zero-sum quasi-invariance rigidity. Every summable shift
preserves the measure class as soon as every zero-sum summable shift does. -/
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Set
open scoped ENNReal
namespace MeasureEquivalenceRigidity
end MeasureEquivalenceRigidity
open MeasureEquivalenceRigidity
open MeasureEquivalenceSolenoid MeasureEquivalenceRootContinuity
  MeasureEquivalenceRNGraph MeasureEquivalenceHellinger
  MeasureEquivalenceErgodicDecomposition
variable {Z : Type*} [MetricSpace Z] [CompactSpace Z] [MeasurableSpace Z]
    [BorelSpace Z]
    [MulAction (Multiplicative CompactSequences) Z]
    [ContinuousSMul (Multiplicative CompactSequences) Z]
    (M : Measure Z) [IsProbabilityMeasure M]
    (hQI : ∀ h : CompactSequences, h ∈ zeroSumSubgroup →
      Multiplicative.ofAdd h ∈ quasiInvariantSubgroup M)

include hQI

theorem solution (a : ℝ) :
    Multiplicative.ofAdd (coordinateShift a) ∈ quasiInvariantSubgroup M := by
  letI : Nonempty Z := nonempty_of_isProbabilityMeasure M
  letI : MulAction rationalZeroSumGroup Z := rationalZeroSumAction
  letI : MeasurableConstSMul rationalZeroSumGroup Z := ⟨fun d =>
    measurable_const_smul (zeroSumGroupHom d.val)⟩
  have hns (d : rationalZeroSumGroup) :
      QuasiMeasurePreserving (fun z : Z => d • z) M M := by
    refine ⟨measurable_const_smul d, ?_⟩
    exact (hQI _ ⟨d.val.toAdd,d.val.toAdd.property,rfl⟩).1
  have hcomm (k : Multiplicative CompactSequences) (d : rationalZeroSumGroup) (z : Z) :
      k • (d • z) = d • (k • z) := by
    change k • (zeroSumGroupHom d.val • z) = zeroSumGroupHom d.val • (k • z)
    exact smul_comm k _ z
  exact quasiInvariant_of_uniform_invariant_mean_affinity M hns coordinateShiftHom hcomm
    (zeroSumComponentKernel_coordinate_mean M hQI) a
