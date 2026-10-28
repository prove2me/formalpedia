-- Prove2me | Definitions.Def_BenchmarkOperator20261026_InvariantConditional
-- name    : BenchmarkOperator20261026_InvariantConditional
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:26:09.39589+00:00
-- url     : https://prove2.me/theorems/5056f691-b9e5-4243-8a85-ff6b8120d859
-- title:
--   Invariant Conditional
-- statement:
--   Defines the invariant sigma-algebra of a group action, its underlying measurable-space presentation and identity map, and the associated conditional kernels for a finite measure. The required measurable-space and kernel instances are retained. Subsequent theorem nodes establish reconstruction and component properties.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization InvariantConditional.lean, lines 15–109; source SHA-256 18db8be10608de97d850984b7c4ff8902f00cffb313850ed50d0a0f207f194dd. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Condexp

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

/-!
The exact invariant sigma-algebra and its actual conditional-probability
kernel. This module establishes invariance and reconstruction; it does
not assert ergodicity of the component probabilities.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal ProbabilityTheory

namespace MeasureEquivalenceErgodicDecomposition

/-- A separate type for the same points equipped with the invariant
sigma-algebra. It keeps the two measurable-space structures explicit. -/
def InvariantBase (_G Z : Type*) := Z

variable {G Z : Type*} [Group G] [MeasurableSpace Z] [MulAction G Z]

/-- The ambient measurable sets that are exactly invariant under the
whole group form a sigma-algebra. -/
@[reducible] def invariantSigma : MeasurableSpace Z where
  MeasurableSet' s := MeasurableSet s ∧ ∀ g : G, (fun z => g • z) ⁻¹' s = s
  measurableSet_empty := ⟨MeasurableSet.empty, fun _ => rfl⟩
  measurableSet_compl s hs := ⟨hs.1.compl, fun g => by
    rw [preimage_compl, hs.2 g]⟩
  measurableSet_iUnion s hs := ⟨MeasurableSet.iUnion (fun n => (hs n).1), fun g => by
    simp_rw [preimage_iUnion, fun n => (hs n).2 g]⟩

theorem invariantSigma_le : invariantSigma (G := G) (Z := Z) ≤ ‹MeasurableSpace Z› :=
  fun _ h => h.1



instance invariantBaseMeasurableSpace : MeasurableSpace (InvariantBase G Z) :=
  invariantSigma (G := G) (Z := Z)

/-- The identity on points, with the invariant sigma-algebra as target. -/
def invariantBaseMap (z : Z) : InvariantBase G Z := z





section Conditional

variable [StandardBorelSpace Z] (μ : Measure Z) [IsFiniteMeasure μ]

/-- The actual regular conditional probability kernel of the identity
given the exact invariant sigma-algebra, viewed on the ambient space. -/
noncomputable def invariantConditionalKernel : Kernel Z Z :=
  Kernel.comap (condExpKernel μ (invariantSigma (G := G))) id
    (measurable_id'' (invariantSigma_le (G := G)))

instance invariantConditionalKernel_markov :
    IsMarkovKernel (invariantConditionalKernel (G := G) μ) := by
  unfold invariantConditionalKernel
  infer_instance







/-- The conditional kernel with its smaller measurable source kept
explicit as a distinct type. -/
noncomputable def invariantBaseKernel : Kernel (InvariantBase G Z) Z :=
  condExpKernel (Ω := Z) μ (invariantSigma (G := G))

instance invariantBaseKernel_markov : IsMarkovKernel (invariantBaseKernel (G := G) μ) := by
  change IsMarkovKernel (condExpKernel (Ω := Z) μ (invariantSigma (G := G)))
  infer_instance













end Conditional

end MeasureEquivalenceErgodicDecomposition


