-- Prove2me | Theorems.Thm_MeasureEquivalenceRigidity_zeroSum_not_reducible_to_measure_equivalence
-- name    : MeasureEquivalenceRigidity.zeroSum_not_reducible_to_measure_equivalence
-- status  : Proved
-- author  : @username
-- created : 2026-10-26T11:12:24.188688+00:00
-- url     : https://prove2.me/theorems/459211af-a1cb-44ea-a044-dcfdda1fa7c9
-- title:
--   The compact zero-sum coset relation does not reduce to measure equivalence
-- statement:
--   Let $K=\widehat{\mathbb Q}^{\mathbb N}$ and let $H\leq K$ be the image of the summable real sequences with zero total under the coordinate solenoid embedding. There is no Borel map $f:K\to\mathcal P(2^{\mathbb N})$ satisfying
--   $$f(x)\sim f(y)\quad\Longleftrightarrow\quad x-y\in H.$$
--   Thus the actual compact zero-sum coset relation is not Borel reducible to mutual absolute continuity of probability measures on Cantor space. This supplies the obstruction used for strict operator complexity.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); supporting declaration MeasureEquivalenceRigidity.zeroSum_not_reducible_to_measure_equivalence in ZeroSumNonreduction.lean, lines 60–82; local source SHA-256 8333d70cf178c90a9b08a0d237d3d68bac8d098399a72e59f784b5b60b5395a3. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_CompactAveraging
import Definitions.Def_BenchmarkOperator20261026_HellingerInner
import Definitions.Def_BenchmarkOperator20261026_InvariantConditional
import Definitions.Def_BenchmarkOperator20261026_InvariantGraphGroup
import Definitions.Def_BenchmarkOperator20261026_KernelEquivalence
import Definitions.Def_BenchmarkOperator20261026_MetropolisCoupling
import Definitions.Def_BenchmarkOperator20261026_OrbitMarkov
import Definitions.Def_BenchmarkOperator20261026_RNGraph
import Definitions.Def_BenchmarkOperator20261026_SolenoidGroups
import Definitions.Def_BenchmarkOperator20261026_ZeroSumConditional
import Definitions.Def_BenchmarkOperator20261026_ZeroSumDense
import Definitions.Def_BenchmarkOperator20261026_ZeroSumNonreduction
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
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Haar.Basic
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
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Order.OrderClosed
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

/-! Compact Haar averaging turns a hypothetical reduction of the actual
zero-sum coset relation into a probability whose exact quasi-invariance
subgroup is that zero-sum subgroup. -/
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal Topology
namespace MeasureEquivalenceRigidity
end MeasureEquivalenceRigidity
open MeasureEquivalenceRigidity
open MeasureEquivalenceCompactAveraging MeasureEquivalenceResearch
  MeasureEquivalenceSolenoid MeasureEquivalenceRNGraph

theorem MeasureEquivalenceRigidity.zeroSum_not_reducible_to_measure_equivalence :
    ¬ ∃ f : CompactSequences → ProbabilityMeasure CantorSample,
      Measurable f ∧ ∀ x y,
        EquivalentMeasures (f x : Measure CantorSample) (f y : Measure CantorSample) ↔
          x - y ∈ zeroSumSubgroup := by sorry
