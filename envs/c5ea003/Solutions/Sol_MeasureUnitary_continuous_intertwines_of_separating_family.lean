-- Prove2me | solution 1 for MeasureUnitary.continuous_intertwines_of_separating_family
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T11:42:18.625776+00:00
-- url     : https://prove2.me/submissions/7ef4341a-4fd6-46bf-9608-51b4b0b791e7

import Definitions.Def_BenchmarkOperator20261026_HilbertSequenceTopology
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorDenseFamily
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorTuple
import Definitions.Def_BenchmarkOperator20261026_MeasureL2Constants
import Definitions.Def_BenchmarkOperator20261026_MeasurePullbackMultipliers
import Definitions.Def_BenchmarkOperator20261026_OperatorFreeGroup
import Definitions.Def_BenchmarkOperator20261026_OperatorStrongUnitary
import Definitions.Def_BenchmarkOperator20261026_RestrictedCompatibility
import Definitions.Def_BenchmarkOperator20261026_RestrictedDensity
import Definitions.Def_BenchmarkOperator20261026_RestrictedFiniteModulus
import Definitions.Def_BenchmarkOperator20261026_RestrictedPhaseFamily
import Definitions.Def_BenchmarkOperator20261026_RestrictedProduct
import Definitions.Def_BenchmarkOperator20261026_RestrictedStages
import Definitions.Def_BenchmarkOperator20261026_SolenoidGroups
import Definitions.Def_BenchmarkOperator20261026_SumFiberCoordinates
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Nat.Nth
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Theorems.Thm_MeasureEquivalenceRestrictedPhase_starAlgHom_eq_of_separating_family

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

/-! Genuine unitary intertwiners of a separating continuous family
intertwine every pulled-back continuous multiplier. The two underlying
measure spaces may be arbitrary and have different Hilbert coefficient fibers. -/
open MeasureTheory
namespace MeasureUnitary
end MeasureUnitary
open MeasureUnitary
variable {Ω Ψ K : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
  [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [CompactSpace K] [SecondCountableTopology K]
  (μ : Measure Ω) (ν : Measure Ψ) (q : Ω → K) (r : Ψ → K) (hq : Measurable q) (hr : Measurable r)
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem solution {I : Type*}
    (c : I → C(K, ℂ)) (hsep : ∀ x y : K, x ≠ y → ∃ i, c i x ≠ c i y)
    (U : Lp E 2 μ ≃ₗᵢ[ℂ] Lp F 2 ν)
    (hU : ∀ i f, U (pullbackMultiplierL2 μ q hq (c i) f) =
      pullbackMultiplierL2 ν r hr (c i) (U f)) :
    ∀ g f, U (pullbackMultiplierL2 μ q hq g f) = pullbackMultiplierL2 ν r hr g (U f) := by
  let φ : C(K, ℂ) →⋆ₐ[ℂ] (Lp F 2 ν →L[ℂ] Lp F 2 ν) :=
    (U.conjStarAlgEquiv : (Lp E 2 μ →L[ℂ] Lp E 2 μ) →⋆ₐ[ℂ]
      (Lp F 2 ν →L[ℂ] Lp F 2 ν)).comp (pullbackMultiplierStarAlgHom (E := E) μ q hq)
  let ψ : C(K, ℂ) →⋆ₐ[ℂ] (Lp F 2 ν →L[ℂ] Lp F 2 ν) := pullbackMultiplierStarAlgHom ν r hr
  have heq : φ = ψ := by
    apply MeasureEquivalenceRestrictedPhase.starAlgHom_eq_of_separating_family φ ψ
      (U.toContinuousLinearEquiv.conjContinuousAlgEquiv.continuous.comp (pullbackMultiplierL2 μ q hq).continuous)
      (pullbackMultiplierL2 ν r hr).continuous c hsep
    intro i
    apply ContinuousLinearMap.ext
    intro f
    change U (pullbackMultiplierL2 μ q hq (c i) (U.symm f)) = pullbackMultiplierL2 ν r hr (c i) f
    simpa using hU i (U.symm f)
  intro g f
  have h := congrArg (fun H : C(K, ℂ) →⋆ₐ[ℂ] (Lp F 2 ν →L[ℂ] Lp F 2 ν) => H g (U f)) heq
  change U (pullbackMultiplierL2 μ q hq g (U.symm (U f))) = pullbackMultiplierL2 ν r hr g (U f) at h
  simpa using h
