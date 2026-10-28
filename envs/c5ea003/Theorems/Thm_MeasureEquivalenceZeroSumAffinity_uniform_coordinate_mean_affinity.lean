-- Prove2me | Theorems.Thm_MeasureEquivalenceZeroSumAffinity_uniform_coordinate_mean_affinity
-- name    : MeasureEquivalenceZeroSumAffinity.uniform_coordinate_mean_affinity
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T11:11:06.122986+00:00
-- url     : https://prove2.me/theorems/9beecef8-2387-4fce-8ba1-6ad006e54bd3
-- title:
--   Compact limits transfer the mean-affinity bound to coordinate translations
-- statement:
--   Let the compact sequence-solenoid group act continuously on a compact metric Borel space $Z$. Let $M$ be a probability measure quasi-invariant under the embedded zero-sum subgroup, and let $\kappa_x$ be a measurable probability kernel. Assume that for each summable zero-sum shift $h$,
--   $$\operatorname{Aff}(M,\iota(h)_*M)=
--   \int\operatorname{Aff}(\kappa_x,\iota(h)_*\kappa_x)\,dM(x).$$
--   Then for every $\varepsilon>0$, some $\delta>0$ satisfies
--   $$|a|<\delta\quad\Longrightarrow\quad
--   \int\operatorname{Aff}(\kappa_x,\iota(ae_0)_*\kappa_x)\,dM(x)\geq1-\varepsilon.$$
--   This is the compact-limit step from zero-sum shifts to a single coordinate.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration MeasureEquivalenceZeroSumAffinity.uniform_coordinate_mean_affinity in CoordinateAffinity.lean, lines 29–57; local source SHA-256 e7707b28e9335d50a2c613371baf62076f824e27bf5c6b56888afd775d2af0d5. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

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

theorem MeasureEquivalenceZeroSumAffinity.uniform_coordinate_mean_affinity (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : ℝ, |a| < δ →
      1 - ε ≤ ∫ x, affinity (κ x) ((κ x).map
        (fun z => Multiplicative.ofAdd (coordinateShift a) • z)) ∂M := by sorry
