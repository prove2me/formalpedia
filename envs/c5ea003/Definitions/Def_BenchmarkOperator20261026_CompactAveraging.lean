-- Prove2me | Definitions.Def_BenchmarkOperator20261026_CompactAveraging
-- name    : BenchmarkOperator20261026_CompactAveraging
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:25:24.615988+00:00
-- url     : https://prove2.me/theorems/a741efef-57c3-4e9d-980c-44762771ef0a
-- title:
--   Compact Averaging
-- statement:
--   Defines the Markov kernel associated with a Borel family of probability measures, normalized compact Haar measure, and the resulting averaged measure for the translation action. The kernel evaluation identity and the probability instances needed for these constructions are included. These objects are used in the later compact-averaging obstruction.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization CompactAveraging.lean, lines 28–99; source SHA-256 fc7ccc9955427115dd3981dc5c32119522747da6a9b4bc95599b1e7c78d9b4b0. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Topology.Algebra.MulAction

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

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped Topology ENNReal

noncomputable section

namespace MeasureEquivalenceCompactAveraging

/-!
`ProbabilityMeasure Y` carries mathlib's canonical evaluation/Giry measurable
structure. A measurable probability-valued map therefore supplies an actual
Markov kernel without any extra kernel hypothesis. The Haar normalization,
joint probability, and exact translation quasi-invariance are constructed
below, including the concrete compact torus and a continuous action adapter.
-/

open MeasureEquivalenceResearch

section Kernel

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def probabilityKernel (f : X → ProbabilityMeasure Y) (hf : Measurable f) : Kernel X Y where
  toFun x := (f x : Measure Y)
  measurable' := measurable_subtype_coe.comp hf

@[simp] lemma probabilityKernel_apply (f : X → ProbabilityMeasure Y) (hf : Measurable f)
    (x : X) : probabilityKernel f hf x = (f x : Measure Y) := rfl

instance probabilityKernel_markov (f : X → ProbabilityMeasure Y) (hf : Measurable f) :
    IsMarkovKernel (probabilityKernel f hf) where
  isProbabilityMeasure x := (f x).property

def averagedMeasure (μ : Measure X) (f : X → ProbabilityMeasure Y) (hf : Measurable f) :
    Measure (X × Y) := μ ⊗ₘ probabilityKernel f hf

instance averagedMeasure_probability (μ : Measure X) [IsProbabilityMeasure μ]
    (f : X → ProbabilityMeasure Y) (hf : Measurable f) :
    IsProbabilityMeasure (averagedMeasure μ f hf) := by
  unfold averagedMeasure
  infer_instance



end Kernel

section CompactGroup

variable (G : Type*) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- Haar measure normalized on the actual compact whole group. -/
def compactHaar : Measure G := Measure.addHaarMeasure (⊤ : PositiveCompacts G)

instance compactHaar_probability : IsProbabilityMeasure (compactHaar G) := by
  constructor
  simpa [compactHaar] using
    (Measure.addHaarMeasure_self (K₀ := (⊤ : PositiveCompacts G)))

instance compactHaar_invariant : Measure.IsAddLeftInvariant (compactHaar G) := by
  unfold compactHaar
  infer_instance

variable {G} {Y : Type*} [MeasurableSpace Y]
    [MeasurableSpace.CountableOrCountablyGenerated G Y]



end CompactGroup

section Action

/-- The multiplicative-tag action used to feed the additive averaging measure to RNGraph. -/
abbrev baseTranslationAction (G Y : Type*) [AddMonoid G] :
    MulAction (Multiplicative G) (G × Y) where
  smul g z := (g.toAdd + z.1, z.2)
  one_smul z := by
    change (0 + z.1, z.2) = z
    simp
  mul_smul g h z := by
    change (g.toAdd + h.toAdd + z.1, z.2) = (g.toAdd + (h.toAdd + z.1), z.2)
    rw [add_assoc]





end Action



















end MeasureEquivalenceCompactAveraging


