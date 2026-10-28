-- Prove2me | Definitions.Def_BenchmarkOperator20261026_HilbertSequenceTopology
-- name    : BenchmarkOperator20261026_HilbertSequenceTopology
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:31:53.816879+00:00
-- url     : https://prove2.me/theorems/5df0597e-6951-4243-8421-883a59511d95
-- title:
--   Hilbert Sequence Topology
-- statement:
--   Defines finite-coordinate truncations into the canonical complex $\ell_2$ space and retains their continuity. The separability and Polish-space instances constructed from these truncations are included. These are the ambient topology data for the later Borel coordinate arguments.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization HilbertSequenceTopology.lean, lines 14–32; source SHA-256 1917b8b55b193ca6a89d5be04be80a4bcb38a023f2d03cabab4a595da4e7ba89. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_OperatorFreeGroup
import Definitions.Def_BenchmarkOperator20261026_OperatorStrongUnitary
import Definitions.Def_BenchmarkOperator20261026_OperatorTargets
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

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

/-! The canonical Hilbert space has its actual norm Polish topology;
its coordinate map is a measurable embedding for this topology. -/

open Filter Topology TopologicalSpace Set
open scoped Topology ENNReal

namespace OperatorCoding

noncomputable section

def hilbertFiniteTruncation (s : Finset ℕ) (x : ℕ → ℂ) : CanonicalHilbert :=
  ∑ i ∈ s, lp.single 2 i (x i)

theorem hilbertFiniteTruncation_continuous (s : Finset ℕ) :
    Continuous (hilbertFiniteTruncation s) := by
  apply continuous_finsetSum
  intro i _hi
  exact (lp.singleContinuousAddMonoidHom (fun _ : ℕ => ℂ) 2 i).continuous.comp
    (continuous_apply i)

instance canonicalHilbert_separable : SeparableSpace CanonicalHilbert := by
  have hd : Dense (⋃ s : Finset ℕ, Set.range (hilbertFiniteTruncation s)) := by
    intro x
    apply mem_closure_of_tendsto (lp.hasSum_single (by norm_num : (2:ℝ≥0∞) ≠ ⊤) x)
    exact Filter.Eventually.of_forall (fun s => Set.mem_iUnion.mpr ⟨s, ⟨(x:ℕ→ℂ), rfl⟩⟩)
  apply hd.isSeparable_iff.mp
  exact IsSeparable.iUnion (fun s => isSeparable_range (hilbertFiniteTruncation_continuous s))

instance canonicalHilbert_polish : PolishSpace CanonicalHilbert := inferInstance







end
end OperatorCoding


