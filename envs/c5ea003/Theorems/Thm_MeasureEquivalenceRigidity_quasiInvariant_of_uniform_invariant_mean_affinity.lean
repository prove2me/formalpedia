-- Prove2me | Theorems.Thm_MeasureEquivalenceRigidity_quasiInvariant_of_uniform_invariant_mean_affinity
-- name    : MeasureEquivalenceRigidity.quasiInvariant_of_uniform_invariant_mean_affinity
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T11:10:29.412671+00:00
-- url     : https://prove2.me/theorems/a042c8a3-1cec-47f2-a277-c757e5880bfe
-- title:
--   Uniform invariant-component affinity implies global quasi-invariance
-- statement:
--   Let a countable group $G$ act nonsingularly on a Borel probability space $(Z,\mu)$, with $Z$ nonempty and standard Borel. Let a commutative group $K$, equipped with a topology, act continuously on $Z$ and commute with the $G$-action. Write $\kappa_x$ for the invariant conditional probability kernel, and let $g:\mathbb R\to K$ be a homomorphism. If
--   $$\forall\varepsilon>0\ \exists\delta>0\ \forall |b|<\delta:\quad
--   1-\varepsilon\leq\int\operatorname{Aff}(\kappa_x,g(b)_*\kappa_x)\,d\mu(x),$$
--   then for every fixed $a\in\mathbb R$ the measures $g(a)_*\mu$ and $\mu$ have the same null sets. This upgrades component rigidity to the original measure.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration MeasureEquivalenceRigidity.quasiInvariant_of_uniform_invariant_mean_affinity in ComponentRigidityRoots.lean, lines 208–232; local source SHA-256 24ec0c9b1da33e69de220995790006d9c2544459a304dbb277860fefd7f782ce. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_HellingerAffinity
import Definitions.Def_BenchmarkOperator20261026_InvariantConditional
import Definitions.Def_BenchmarkOperator20261026_MetropolisCoupling
import Definitions.Def_BenchmarkOperator20261026_OrbitMarkov
import Definitions.Def_BenchmarkOperator20261026_RNGraph
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
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
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Order.OrderClosed

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

/-! Actual component quasi-invariance is detected by Hellinger affinity,
and vanishing mean deficits along roots give component quasi-invariance. -/
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter
open scoped ENNReal Topology
namespace MeasureEquivalenceRigidity
end MeasureEquivalenceRigidity
open MeasureEquivalenceRigidity
open MeasureEquivalenceHellinger MeasureEquivalenceErgodicDecomposition
variable {K G Z : Type*} [CommGroup K] [TopologicalSpace K]
    [Group G] [Countable G]
    [MeasurableSpace Z] [TopologicalSpace Z] [BorelSpace Z]
    [StandardBorelSpace Z] [Nonempty Z] [MeasurableEq Z]
    [MulAction K Z] [ContinuousSMul K Z] [MulAction G Z] [MeasurableConstSMul G Z]
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (hns : ∀ d : G, QuasiMeasurePreserving (fun z : Z => d • z) μ μ)

include hns

theorem MeasureEquivalenceRigidity.quasiInvariant_of_uniform_invariant_mean_affinity
    (g : ℝ →+ Additive K)
    (hcomm : ∀ (k : K) (d : G) (z : Z), k • (d • z) = d • (k • z))
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ b : ℝ, |b| < δ → 1 - ε ≤ ∫ x,
        affinity (invariantConditionalKernel (G := G) μ x)
          ((invariantConditionalKernel (G := G) μ x).map
            (fun z => Additive.toMul (g b) • z)) ∂μ)
    (a : ℝ) :
    Additive.toMul (g a) ∈ MeasureEquivalenceRNGraph.quasiInvariantSubgroup μ := by sorry
