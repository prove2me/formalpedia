-- Prove2me | Theorems.Thm_MeasureEquivalenceRigidity_ae_componentQI_of_uniform_mean_affinity
-- name    : MeasureEquivalenceRigidity.ae_componentQI_of_uniform_mean_affinity
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T11:09:58.781128+00:00
-- url     : https://prove2.me/theorems/d3f2a4ff-2d2d-4a17-a696-7d14d4130dcb
-- title:
--   Uniform mean affinity near zero forces each real displacement into component stabilizers
-- statement:
--   Let $K$ be a commutative group equipped with a topology and acting continuously on a Borel space $Z$. Let $\eta$ be a probability measure and $\kappa_y$ a measurable family of probability measures on $Z$. Let $g:\mathbb R\to K$ be a homomorphism. Assume the kernel-integral countability condition and the simultaneous component criterion
--   $$\operatorname{Aff}(\kappa_y,k_*\kappa_y)=0\quad\Longleftrightarrow\quad k\notin Q_y$$
--   for every $k$, outside one null set. If the averaged affinity tends uniformly to one for sufficiently small real parameters, in the sense
--   $$\forall\varepsilon>0\ \exists\delta>0\ \forall |b|<\delta:\quad
--   1-\varepsilon\leq\int\operatorname{Aff}(\kappa_y,g(b)_*\kappa_y)\,d\eta(y),$$
--   then for each fixed $a\in\mathbb R$, $g(a)\in Q_y$ almost everywhere. The exceptional set may depend on $a$.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration MeasureEquivalenceRigidity.ae_componentQI_of_uniform_mean_affinity in ComponentRigidityRoots.lean, lines 140–179; local source SHA-256 24ec0c9b1da33e69de220995790006d9c2544459a304dbb277860fefd7f782ce. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_ComponentQuasiInvariance
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
variable {K Y Z : Type*} [CommGroup K] [TopologicalSpace K]
    [MeasurableSpace Y] [MeasurableSpace Z] [TopologicalSpace Z] [BorelSpace Z]
    [MulAction K Z] [ContinuousSMul K Z]
    [MeasurableSpace.CountableOrCountablyGenerated Y Z]
    (η : Measure Y) [IsProbabilityMeasure η]
    (κ : Kernel Y Z) [IsMarkovKernel κ]

theorem MeasureEquivalenceRigidity.ae_componentQI_of_uniform_mean_affinity
    (g : ℝ →+ Additive K)
    (hzero : ∀ᵐ y ∂η, ∀ k : K,
      affinity (κ y) ((κ y).map (fun z => k • z)) = 0 ↔ k ∉ componentQI κ y)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ b : ℝ, |b| < δ → 1 - ε ≤ ∫ y,
        affinity (κ y) ((κ y).map (fun z => Additive.toMul (g b) • z)) ∂η)
    (a : ℝ) :
    ∀ᵐ y ∂η, Additive.toMul (g a) ∈ componentQI κ y := by sorry
