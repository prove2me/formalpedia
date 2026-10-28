-- Prove2me | Definitions.Def_BenchmarkOperator20261026_RNGraph
-- name    : BenchmarkOperator20261026_RNGraph
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:26:30.017403+00:00
-- url     : https://prove2.me/theorems/ecbc1c91-363e-4e98-a5a1-84336019752f
-- title:
--   RNGraph
-- statement:
--   Defines the finite-measure orbit of a probability under a continuous group action, its measure-class stabilizer subgroup, the root-density feature map, and the associated graph map. The orbit probability instance and orbit-composition identity are retained. Closedness and continuity assertions occur in later theorem nodes.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization RNGraph.lean, lines 34–127; source SHA-256 cc8db11a6a4107f7ae6cf4e29673db3d07f1805fcbb02b5944b7deccfb1ca590. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_DensitySquare
import Definitions.Def_BenchmarkOperator20261026_HellingerTransport
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
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.MetricSpace.Polish

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

open MeasureTheory Filter Set
open scoped Topology

namespace MeasureEquivalenceRNGraph

open MeasureEquivalenceDensity MeasureEquivalenceHellinger

variable {Z : Type*} [MeasurableSpace Z]



section Action

variable {K : Type*} [CommGroup K] [TopologicalSpace K]
    [TopologicalSpace Z] [BorelSpace Z] [MulAction K Z] [ContinuousSMul K Z]
    (M : Measure Z) [IsProbabilityMeasure M]

noncomputable def orbit (g : K) : FiniteMeasure Z :=
  ⟨M.map (fun z => g • z), inferInstance⟩

instance orbit_isProbability (g : K) : IsProbabilityMeasure (orbit M g : Measure Z) := by
  change IsProbabilityMeasure (M.map (fun z => g • z))
  exact M.isProbabilityMeasure_map (measurable_const_smul g).aemeasurable



omit [IsProbabilityMeasure M] in
theorem map_orbit (g h : K) :
    (M.map (fun z => h • z)).map (fun z => g • z) = M.map (fun z => (g * h) • z) := by
  rw [Measure.map_map (measurable_const_smul g) (measurable_const_smul h)]
  congr 1
  funext z
  exact (mul_smul g h z).symm

/-- Exact quasi-invariance subgroup, tested by forward and inverse one-sided AC. -/
def quasiInvariantSubgroup : Subgroup K where
  carrier := {g | M.map (fun z => g • z) ≪ M ∧ M.map (fun z => g⁻¹ • z) ≪ M}
  one_mem' := by simpa using (And.intro (Measure.AbsolutelyContinuous.refl M) (Measure.AbsolutelyContinuous.refl M))
  mul_mem' := by
    intro g h hg hh
    constructor
    · rw [← map_orbit M g h]
      exact ((MeasurableEquiv.smul g).measurableEmbedding.absolutelyContinuous_map hh.1).trans hg.1
    · rw [mul_inv_rev, ← map_orbit M h⁻¹ g⁻¹]
      exact ((MeasurableEquiv.smul h⁻¹).measurableEmbedding.absolutelyContinuous_map hg.2).trans hh.2
  inv_mem' := by
    intro g hg
    exact ⟨hg.2, by simpa only [inv_inv] using hg.1⟩



noncomputable def feature (h : quasiInvariantSubgroup (K := K) M) : positiveUnitSphere M :=
  ⟨root (orbit M (h : K) : Measure Z) M,
    root_nonnegative _ _, root_probability_norm _ _ h.property.1⟩







end Action

section Graph

variable {K : Type*} [CommGroup K] [MetricSpace K] [IsTopologicalGroup K]
    [TopologicalSpace Z] [PolishSpace Z] [BorelSpace Z]
    [MulAction K Z] [ContinuousSMul K Z] (M : Measure Z) [IsProbabilityMeasure M]

noncomputable def graphMap (h : quasiInvariantSubgroup (K := K) M) :
    K × positiveUnitSphere M := ((h : K), feature M h)







end Graph

end MeasureEquivalenceRNGraph


