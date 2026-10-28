-- Prove2me | solution 1 for OperatorCoding.theorem_13_proved
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T13:39:18.170975+00:00
-- url     : https://prove2.me/submissions/ea308b16-2745-4a17-888e-2eefa39ba47c

import Definitions.Def_BenchmarkOperator20261026_CompactAveraging
import Definitions.Def_BenchmarkOperator20261026_HellingerInner
import Definitions.Def_BenchmarkOperator20261026_HilbertSequenceTopology
import Definitions.Def_BenchmarkOperator20261026_InducedCornerTransport
import Definitions.Def_BenchmarkOperator20261026_InducedCornerUnitary
import Definitions.Def_BenchmarkOperator20261026_InvariantConditional
import Definitions.Def_BenchmarkOperator20261026_InvariantGraphGroup
import Definitions.Def_BenchmarkOperator20261026_KernelEquivalence
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorAmplified
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorBorel
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorDenseFamily
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorGram
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorTuple
import Definitions.Def_BenchmarkOperator20261026_MeasureGramSchmidtBorel
import Definitions.Def_BenchmarkOperator20261026_MeasureInducedOperatorCode
import Definitions.Def_BenchmarkOperator20261026_MeasureL2Constants
import Definitions.Def_BenchmarkOperator20261026_MeasureOperatorReduction
import Definitions.Def_BenchmarkOperator20261026_MeasurePullbackMultipliers
import Definitions.Def_BenchmarkOperator20261026_MeasureUnitaryDensity
import Definitions.Def_BenchmarkOperator20261026_MeasureUnitaryMultipliers
import Definitions.Def_BenchmarkOperator20261026_MeasureUnitaryRN
import Definitions.Def_BenchmarkOperator20261026_MeasureVariableGramSchmidt
import Definitions.Def_BenchmarkOperator20261026_MetropolisCoupling
import Definitions.Def_BenchmarkOperator20261026_OperatorAmplification
import Definitions.Def_BenchmarkOperator20261026_OperatorBireduction
import Definitions.Def_BenchmarkOperator20261026_OperatorBlocks
import Definitions.Def_BenchmarkOperator20261026_OperatorConjugation
import Definitions.Def_BenchmarkOperator20261026_OperatorEigenspaces
import Definitions.Def_BenchmarkOperator20261026_OperatorFreeGroup
import Definitions.Def_BenchmarkOperator20261026_OperatorHilbertFlatten
import Definitions.Def_BenchmarkOperator20261026_OperatorNormalization
import Definitions.Def_BenchmarkOperator20261026_OperatorSeries
import Definitions.Def_BenchmarkOperator20261026_OperatorStrongUnitary
import Definitions.Def_BenchmarkOperator20261026_OperatorTargets
import Definitions.Def_BenchmarkOperator20261026_OperatorUnitaryBorel
import Definitions.Def_BenchmarkOperator20261026_OrbitMarkov
import Definitions.Def_BenchmarkOperator20261026_PiecewiseMeasureTransport
import Definitions.Def_BenchmarkOperator20261026_RNGraph
import Definitions.Def_BenchmarkOperator20261026_RestrictedAction
import Definitions.Def_BenchmarkOperator20261026_RestrictedCompactMeasure
import Definitions.Def_BenchmarkOperator20261026_RestrictedCompatibility
import Definitions.Def_BenchmarkOperator20261026_RestrictedDensity
import Definitions.Def_BenchmarkOperator20261026_RestrictedDeparture
import Definitions.Def_BenchmarkOperator20261026_RestrictedFiniteModulus
import Definitions.Def_BenchmarkOperator20261026_RestrictedFullReflection
import Definitions.Def_BenchmarkOperator20261026_RestrictedInducedFamily
import Definitions.Def_BenchmarkOperator20261026_RestrictedInducedReflection
import Definitions.Def_BenchmarkOperator20261026_RestrictedInducedSpectral
import Definitions.Def_BenchmarkOperator20261026_RestrictedInducedTuple
import Definitions.Def_BenchmarkOperator20261026_RestrictedModulus
import Definitions.Def_BenchmarkOperator20261026_RestrictedPhaseFamily
import Definitions.Def_BenchmarkOperator20261026_RestrictedProduct
import Definitions.Def_BenchmarkOperator20261026_RestrictedSpectralClass
import Definitions.Def_BenchmarkOperator20261026_RestrictedStages
import Definitions.Def_BenchmarkOperator20261026_RestrictedTranslatedCorner
import Definitions.Def_BenchmarkOperator20261026_RestrictedTranslationIntertwining
import Definitions.Def_BenchmarkOperator20261026_ScalarMeasureNormalization
import Definitions.Def_BenchmarkOperator20261026_SeparatingMultiplierIntertwining
import Definitions.Def_BenchmarkOperator20261026_SolenoidGroups
import Definitions.Def_BenchmarkOperator20261026_SumFiberCoordinates
import Definitions.Def_BenchmarkOperator20261026_VectorSpectralState
import Definitions.Def_BenchmarkOperator20261026_ZeroSumConditional
import Definitions.Def_BenchmarkOperator20261026_ZeroSumDense
import Definitions.Def_BenchmarkOperator20261026_ZeroSumNonreduction
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Nat
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Kernel.Disintegration.Unique
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_MeasureEquivalenceRestrictedPhase_exists_inducedTuple_intertwiner_of_zeroSum
import Theorems.Thm_MeasureEquivalenceRestrictedPhase_total_eq_zero_of_normalized_intertwiner
import Theorems.Thm_MeasureEquivalenceRestrictedProduct_null_of_invariant_and_base_null
import Theorems.Thm_MeasureEquivalenceRigidity_zeroSum_not_reducible_to_measure_equivalence
import Theorems.Thm_MeasureUnitary_continuous_intertwines_of_separating_family
import Theorems.Thm_MeasureUnitary_measurable_nat_nth
import Theorems.Thm_MeasureUnitary_push_measures_equivalent_of_intertwines_continuous
import Theorems.Thm_MeasureUnitary_vectorCantorMultiplier_fundamental
import Theorems.Thm_OperatorCoding_tupleImaginaryPart_star_entry
import Theorems.Thm_OperatorCoding_tupleImaginaryPart_tuple_entry

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

-- Preserved source skeleton: HilbertSequenceTopology
section
/-! The canonical Hilbert space has its actual norm Polish topology;
its coordinate map is a measurable embedding for this topology. -/

open Filter Topology TopologicalSpace Set
open scoped Topology ENNReal

namespace OperatorCoding

noncomputable section











theorem canonicalHilbert_coordinates_continuous :
    Continuous (fun x : CanonicalHilbert => (x : ℕ → ℂ)) := by
  apply continuous_pi
  intro i
  exact (lp.lipschitzWith_one_eval (E := fun _ : ℕ => ℂ) 2 i).continuous

theorem canonicalHilbert_coordinates_measurableEmbedding :
    @MeasurableEmbedding CanonicalHilbert (ℕ → ℂ) (borel CanonicalHilbert)
      inferInstance (fun x => (x : ℕ → ℂ)) := by
  letI : MeasurableSpace CanonicalHilbert := borel CanonicalHilbert
  letI : BorelSpace CanonicalHilbert := ⟨rfl⟩
  exact canonicalHilbert_coordinates_continuous.measurableEmbedding (fun _ _ h => lp.ext h)

end
end OperatorCoding

end

-- Preserved source skeleton: MeasureUnitaryMultipliers
section
/-! Genuine multiplication unitaries in complex L², and their natural
intertwining by the square-root Radon–Nikodym unitary. -/

open MeasureTheory Filter
open scoped ENNReal

namespace MeasureUnitary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
  (c : α → ℂ) (hc : Measurable c) (hnorm : ∀ x, ‖c x‖ = 1)

include hc hnorm















variable (ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]

theorem rnWeightedEquiv_intertwines_phase (hμν : μ ≪ ν) (hνμ : ν ≪ μ) (f : Lp E 2 μ) :
    rnWeightedEquiv μ ν hμν hνμ (phaseEquiv μ c hc hnorm f) =
      phaseEquiv ν c hc hnorm (rnWeightedEquiv μ ν hμν hνμ f) := by
  change rnWeightedMap μ ν hμν hνμ (phaseMap μ c hc hnorm f) =
    phaseMap ν c hc hnorm (rnWeightedMap μ ν hμν hνμ f)
  apply Lp.ext
  filter_upwards [rnWeightedMap_coe μ ν hμν hνμ (phaseMap μ c hc hnorm f),
    hνμ.ae_eq (phaseMap_coe μ c hc hnorm f),
    phaseMap_coe ν c hc hnorm (rnWeightedMap μ ν hμν hνμ f),
    rnWeightedMap_coe μ ν hμν hνμ f] with x hleft hphase hright hRN
  rw [hleft, hphase, hright, hRN]
  change rnWeight μ ν x • (c x • f x) = c x • (rnWeight μ ν x • f x)
  exact smul_comm _ _ _

end MeasureUnitary

end

-- Preserved source skeleton: InducedCornerUnitary
section
/-! Actual multiplication and group-shift unitaries on the induced L2
corner modules, and their simultaneous intertwining for equal finite mass. -/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal

namespace MeasureEquivalenceInducedCorners

open MeasureEquivalenceEquidecomposition MeasureUnitary

noncomputable section

variable {G Z : Type*} [Group G] [Countable G]
    [MeasurableSpace G] [MeasurableSingletonClass G]
    [MeasurableSpace Z] [MulAction G Z] [MeasurableConstSMul G Z]
    (μ : Measure Z) [SigmaFinite μ]



omit [SigmaFinite μ] in
theorem inducedPhaseUnitary_coe (A : Set Z) (f : Z → ℂ) (hf : Measurable f)
    (hnorm : ∀ z, ‖f z‖ = 1) (u : Lp ℂ 2 (cornerMeasure (G := G) μ A)) :
    inducedPhaseUnitary μ A f hf hnorm u =ᵐ[cornerMeasure (G := G) μ A]
      (fun p => f (orbitPoint p) • u p) :=
  phaseMap_coe (cornerMeasure (G := G) μ A) (fun p => f (orbitPoint p))
    (hf.comp orbitPoint_measurable) (fun p => hnorm (orbitPoint p)) u











variable (hmp : ∀ g : G, MeasurePreserving (fun z : Z => g • z) μ μ)



end
end MeasureEquivalenceInducedCorners

end

-- Preserved source skeleton: MeasureCantorTuple
section
/-! Countably many genuine L² multiplication unitaries, one for every
clopen finite-coordinate Cantor cylinder. Equivalent measures give
intertwining representations through the actual RN unitary. -/

open MeasureTheory Set

namespace MeasureUnitary


























theorem cantorCylinder_isPiSystem : IsPiSystem (Set.range cantorCylinder) := by
  rw [cantorCylinder_range]
  exact isPiSystem_measurableCylinders

end MeasureUnitary

end

-- Preserved source skeleton: MeasureUnitaryDensity
section
/-! The spectral-class measure attached to an actual L² vector, expressed
without invoking a spectral theorem. Its mass on a set is the square of the
norm of the corresponding multiplication projection. -/

open MeasureTheory Filter Set
open scoped ENNReal

namespace MeasureUnitary

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]









theorem vectorDensityMeasure_absolutelyContinuous (f : Lp E 2 μ) : vectorDensityMeasure μ f ≪ μ :=
  withDensity_absolutelyContinuous μ _







theorem constantVectorL2_density [IsFiniteMeasure μ] (v : E) (hv : ‖v‖ = 1) :
    vectorDensityMeasure μ (constantVectorL2 μ v) = μ := by
  unfold vectorDensityMeasure
  have h : (fun x => ENNReal.ofReal (‖constantVectorL2 μ v x‖ ^ 2)) =ᵐ[μ] fun _ => 1 := by
    filter_upwards [constantVectorL2_coe μ v] with x hx
    rw [hx, hv]
    norm_num
  rw [withDensity_congr_ae h]
  change μ.withDensity 1 = μ
  exact withDensity_one







end MeasureUnitary

end

-- Preserved source skeleton: MeasureCantorAmplified
section
/-! An infinite-multiplicity Cantor representation, on Hilbert-valued L².
The coefficient Hilbert space is fixed, but the measure-dependent L² spaces
are not yet identified with one canonical Hilbert space in a Borel fashion. -/

open MeasureTheory Set Filter
open scoped ENNReal

namespace MeasureUnitary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]





theorem equivalentMeasures_vectorCantorMultiplierEquivalent (μ ν : Measure CantorSpace)
    [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    VectorCantorMultiplierEquivalent E μ ν := by
  refine ⟨rnWeightedEquiv μ ν hμν hνμ, fun k f => ?_⟩
  exact rnWeightedEquiv_intertwines_phase μ (cantorCylinderPhase k)
    (cantorCylinderPhase_measurable k) (cantorCylinderPhase_norm k) ν hμν hνμ f

theorem indicatorL2_vectorCantorMultiplier (μ : Measure CantorSpace) (k : CantorCylinderIndex)
    (f : Lp E 2 μ) :
    indicatorL2 μ (cantorCylinder_measurable k) f =
      (1 / 2 : ℂ) • (f + vectorCantorMultiplier μ k f) := by
  change indicatorL2 μ (cantorCylinder_measurable k) f =
    (1 / 2 : ℂ) • (f + phaseMap μ (cantorCylinderPhase k)
      (cantorCylinderPhase_measurable k) (cantorCylinderPhase_norm k) f)
  apply Lp.ext
  filter_upwards [indicatorL2_coe μ (cantorCylinder_measurable k) f,
    Lp.coeFn_smul (1 / 2 : ℂ) (f + phaseMap μ (cantorCylinderPhase k)
      (cantorCylinderPhase_measurable k) (cantorCylinderPhase_norm k) f),
    Lp.coeFn_add f (phaseMap μ (cantorCylinderPhase k)
      (cantorCylinderPhase_measurable k) (cantorCylinderPhase_norm k) f),
    phaseMap_coe μ (cantorCylinderPhase k) (cantorCylinderPhase_measurable k)
      (cantorCylinderPhase_norm k) f] with x hI hs ha hp
  simp only [Pi.smul_apply, Pi.add_apply] at hs ha
  rw [hI, hs, ha, hp]
  classical
  by_cases hxs : x ∈ cantorCylinder k
  · simp only [cantorCylinderPhase, if_pos hxs, indicator_of_mem hxs, one_smul]
    rw [← two_smul ℂ (f x), smul_smul]
    norm_num
  · simp only [cantorCylinderPhase, if_neg hxs, indicator_of_notMem hxs, neg_one_smul,
      add_neg_cancel, smul_zero]

theorem vectorCantorMultiplier_intertwines_indicators (μ ν : Measure CantorSpace)
    (U : Lp E 2 μ ≃ₗᵢ[ℂ] Lp E 2 ν)
    (hU : ∀ k f, U (vectorCantorMultiplier μ k f) = vectorCantorMultiplier ν k (U f))
    (k : CantorCylinderIndex) (f : Lp E 2 μ) :
    U (indicatorL2 μ (cantorCylinder_measurable k) f) =
      indicatorL2 ν (cantorCylinder_measurable k) (U f) := by
  rw [indicatorL2_vectorCantorMultiplier, U.map_smul, U.map_add, hU,
    ← indicatorL2_vectorCantorMultiplier]

theorem vectorCantorMultiplier_intertwiner_density (μ ν : Measure CantorSpace) [IsFiniteMeasure μ]
    (v : E) (hv : ‖v‖ = 1) (U : Lp E 2 μ ≃ₗᵢ[ℂ] Lp E 2 ν)
    (hU : ∀ k f, U (vectorCantorMultiplier μ k f) = vectorCantorMultiplier ν k (U f)) :
    μ = vectorDensityMeasure ν (U (constantVectorL2 μ v)) := by
  have hmass : ∀ k : CantorCylinderIndex,
      μ (cantorCylinder k) = vectorDensityMeasure ν (U (constantVectorL2 μ v)) (cantorCylinder k) := by
    intro k
    calc
      μ (cantorCylinder k) = vectorDensityMeasure μ (constantVectorL2 μ v) (cantorCylinder k) := by
        rw [constantVectorL2_density μ v hv]
      _ = ENNReal.ofReal (‖indicatorL2 μ (cantorCylinder_measurable k) (constantVectorL2 μ v)‖ ^ 2) :=
        vectorDensityMeasure_apply _ _ _
      _ = ENNReal.ofReal (‖indicatorL2 ν (cantorCylinder_measurable k) (U (constantVectorL2 μ v))‖ ^ 2) := by
        rw [← vectorCantorMultiplier_intertwines_indicators μ ν U hU, U.norm_map]
      _ = vectorDensityMeasure ν (U (constantVectorL2 μ v)) (cantorCylinder k) :=
        (vectorDensityMeasure_apply _ _ _).symm
  apply ext_of_generate_finite (Set.range cantorCylinder) cantorCylinder_generates.symm
    cantorCylinder_isPiSystem
  · rintro s ⟨k, rfl⟩
    exact hmass k
  · have h := hmass (⟨∅, Set.univ⟩ : CantorCylinderIndex)
    simpa [cantorCylinder, cylinder] using h

theorem vectorCantorMultiplier_intertwiner_absolutelyContinuous (μ ν : Measure CantorSpace)
    [IsFiniteMeasure μ] (v : E) (hv : ‖v‖ = 1) (U : Lp E 2 μ ≃ₗᵢ[ℂ] Lp E 2 ν)
    (hU : ∀ k f, U (vectorCantorMultiplier μ k f) = vectorCantorMultiplier ν k (U f)) : μ ≪ ν := by
  rw [vectorCantorMultiplier_intertwiner_density μ ν v hv U hU]
  exact vectorDensityMeasure_absolutelyContinuous ν _

theorem vectorCantorMultiplierEquivalent_iff (μ ν : Measure CantorSpace)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (v : E) (hv : ‖v‖ = 1) :
    VectorCantorMultiplierEquivalent E μ ν ↔ μ ≪ ν ∧ ν ≪ μ := by
  constructor
  · rintro ⟨U, hU⟩
    constructor
    · exact vectorCantorMultiplier_intertwiner_absolutelyContinuous μ ν v hv U hU
    · apply vectorCantorMultiplier_intertwiner_absolutelyContinuous ν μ v hv U.symm
      intro k f
      apply U.injective
      simpa using (hU k (U.symm f)).symm
  · intro h
    exact equivalentMeasures_vectorCantorMultiplierEquivalent μ ν h.1 h.2



theorem canonicalHilbertUnitVector_norm : ‖canonicalHilbertUnitVector‖ = 1 := by
  change ‖(lp.single 2 0 (1 : ℂ) : OperatorCoding.CanonicalHilbert)‖ = 1
  rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  norm_num

theorem amplifiedCantorMultiplierEquivalent_iff (μ ν : Measure CantorSpace)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    VectorCantorMultiplierEquivalent OperatorCoding.CanonicalHilbert μ ν ↔ μ ≪ ν ∧ ν ≪ μ :=
  vectorCantorMultiplierEquivalent_iff μ ν canonicalHilbertUnitVector canonicalHilbertUnitVector_norm

end MeasureUnitary

end

-- Preserved source skeleton: MeasureCantorGram
section
/-! Measurable Gram matrices for the explicit varying-measure L² family.
The parameter measurable structure is the genuine Giry structure on
probability measures, and all entries are actual L² inner products. -/

open MeasureTheory Set Filter
open scoped ENNReal

namespace MeasureUnitary

theorem cantorFundamentalVector_inner (μ : Measure CantorSpace) [IsFiniteMeasure μ]
    (k l : CantorFundamentalIndex) :
    inner ℂ (cantorFundamentalVector μ k) (cantorFundamentalVector μ l) =
      μ.real (cantorCylinder k.1 ∩ cantorCylinder l.1) •
        inner ℂ (lp.single 2 k.2 (1 : ℂ) : OperatorCoding.CanonicalHilbert)
          (lp.single 2 l.2 (1 : ℂ) : OperatorCoding.CanonicalHilbert) :=
  L2.inner_indicatorConstLp_indicatorConstLp (cantorCylinder_measurable k.1)
    (cantorCylinder_measurable l.1) (measure_ne_top μ _) (measure_ne_top μ _) _ _

theorem measurable_cantorFundamentalVector_inner (k l : CantorFundamentalIndex) :
    Measurable (fun μ : ProbabilityMeasure CantorSpace =>
      inner ℂ (cantorFundamentalVector (μ : Measure CantorSpace) k)
        (cantorFundamentalVector (μ : Measure CantorSpace) l)) := by
  simp only [cantorFundamentalVector_inner, measureReal_def]
  exact (((Measure.measurable_coe ((cantorCylinder_measurable k.1).inter
    (cantorCylinder_measurable l.1))).comp measurable_subtype_coe).ennreal_toReal).smul measurable_const

theorem measurable_cantorFundamentalSequence_inner (i j : ℕ) :
    Measurable (fun μ : ProbabilityMeasure CantorSpace =>
      inner ℂ (cantorFundamentalSequence (μ : Measure CantorSpace) i)
        (cantorFundamentalSequence (μ : Measure CantorSpace) j)) :=
  measurable_cantorFundamentalVector_inner (cantorFundamentalEnumeration i) (cantorFundamentalEnumeration j)













end MeasureUnitary

end

-- Preserved source skeleton: MeasureVariableGramSchmidt
section
/-! Gram–Schmidt in genuinely varying Hilbert fibers. Measurability is
deduced from scalar Gram entries, without putting a fictitious common
topology on the different L² spaces. Every constructed section is an actual
finite linear combination of the fundamental sections. -/

open MeasureTheory InnerProductSpace Set

namespace MeasureUnitary

variable {S : Type*} [MeasurableSpace S]
variable {E : S → Type*} [∀ s, NormedAddCommGroup (E s)] [∀ s, InnerProductSpace ℂ (E s)]



theorem finiteBorelSection_raw (f : ∀ s, ℕ → E s) (n : ℕ) :
    FiniteBorelSection f (fun s => f s n) := by
  refine ⟨Unit, inferInstance, (fun _ => n), (fun _ _ => 1),
    (fun _ => measurable_const), ?_⟩
  intro s
  simp

theorem finiteBorelSection_zero (f : ∀ s, ℕ → E s) :
    FiniteBorelSection f (fun s => (0 : E s)) := by
  refine ⟨Empty, inferInstance, Empty.elim, (fun _ => Empty.elim),
    (fun i => Empty.elim i), ?_⟩
  intro s
  simp

theorem FiniteBorelSection.add {f : ∀ s, ℕ → E s} {v w : ∀ s, E s}
    (hv : FiniteBorelSection f v) (hw : FiniteBorelSection f w) :
    FiniteBorelSection f (fun s => v s + w s) := by
  classical
  obtain ⟨I, hI, j, c, hc, hv⟩ := hv
  obtain ⟨J, hJ, k, d, hd, hw⟩ := hw
  letI := hI
  letI := hJ
  refine ⟨I ⊕ J, inferInstance, Sum.elim j k, (fun s => Sum.elim (c s) (d s)), ?_, ?_⟩
  · intro i
    cases i with
    | inl i => exact hc i
    | inr i => exact hd i
  · intro s
    dsimp only
    rw [Fintype.sum_sum_type, hv s, hw s]
    rfl

theorem FiniteBorelSection.smul {f : ∀ s, ℕ → E s} {v : ∀ s, E s}
    (hv : FiniteBorelSection f v) {a : S → ℂ} (ha : Measurable a) :
    FiniteBorelSection f (fun s => a s • v s) := by
  obtain ⟨I, hI, j, c, hc, hv⟩ := hv
  letI := hI
  refine ⟨I, hI, j, (fun s i => a s * c s i), (fun i => ha.mul (hc i)), ?_⟩
  intro s
  dsimp only
  rw [hv s, Finset.smul_sum]
  simp only [smul_smul]

theorem FiniteBorelSection.neg {f : ∀ s, ℕ → E s} {v : ∀ s, E s}
    (hv : FiniteBorelSection f v) : FiniteBorelSection f (fun s => -v s) := by
  simpa only [neg_one_smul] using hv.smul (a := fun _ => (-1 : ℂ)) measurable_const

theorem FiniteBorelSection.sub {f : ∀ s, ℕ → E s} {v w : ∀ s, E s}
    (hv : FiniteBorelSection f v) (hw : FiniteBorelSection f w) :
    FiniteBorelSection f (fun s => v s - w s) := by
  simpa only [sub_eq_add_neg] using hv.add hw.neg

theorem finiteBorelSection_sum {f : ∀ s, ℕ → E s} {I : Type*}
    (t : Finset I) (v : I → ∀ s, E s) (hv : ∀ i ∈ t, FiniteBorelSection f (v i)) :
    FiniteBorelSection f (fun s => ∑ i ∈ t, v i s) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using finiteBorelSection_zero f
  | @insert i t hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hv i (Finset.mem_insert_self _ _)).add (ih (fun j hj => hv j (Finset.mem_insert_of_mem hj)))

theorem FiniteBorelSection.inner_measurable {f : ∀ s, ℕ → E s}
    (hgram : ∀ i j, Measurable (fun s => inner ℂ (f s i) (f s j)))
    {v w : ∀ s, E s} (hv : FiniteBorelSection f v) (hw : FiniteBorelSection f w) :
    Measurable (fun s => inner ℂ (v s) (w s)) := by
  obtain ⟨I, hI, j, c, hc, hv⟩ := hv
  obtain ⟨J, hJ, k, d, hd, hw⟩ := hw
  letI := hI
  letI := hJ
  have heq : (fun s => inner ℂ (v s) (w s)) =
      fun s => ∑ i : I, ∑ l : J, d s l * ((starRingEnd ℂ) (c s i) * inner ℂ (f s (j i)) (f s (k l))) := by
    funext s
    rw [hv s, hw s, sum_inner]
    simp only [inner_sum, inner_smul_left, inner_smul_right]
  rw [heq]
  apply Finset.measurable_sum
  intro i hi
  apply Finset.measurable_sum
  intro l hl
  exact (hd l).mul ((Complex.continuous_conj.measurable.comp (hc i)).mul (hgram (j i) (k l)))

theorem FiniteBorelSection.norm_measurable {f : ∀ s, ℕ → E s}
    (hgram : ∀ i j, Measurable (fun s => inner ℂ (f s i) (f s j)))
    {v : ∀ s, E s} (hv : FiniteBorelSection f v) : Measurable (fun s => ‖v s‖) := by
  have hm := (Complex.continuous_re.measurable.comp (hv.inner_measurable hgram hv)).sqrt
  convert hm using 1
  funext s
  change ‖v s‖ = Real.sqrt (RCLike.re (inner ℂ (v s) (v s)))
  rw [← norm_sq_eq_re_inner (𝕜 := ℂ), Real.sqrt_sq (norm_nonneg _)]

theorem variableGramSchmidt_finiteBorelSection (f : ∀ s, ℕ → E s)
    (hgram : ∀ i j, Measurable (fun s => inner ℂ (f s i) (f s j))) (n : ℕ) :
    FiniteBorelSection f (fun s => gramSchmidt ℂ (f s) n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have heq : (fun s => gramSchmidt ℂ (f s) n) = fun s => f s n -
        ∑ i ∈ Finset.Iio n,
          (inner ℂ (gramSchmidt ℂ (f s) i) (f s n) /
            ((‖gramSchmidt ℂ (f s) i‖ ^ 2 : ℝ) : ℂ)) • gramSchmidt ℂ (f s) i := by
      funext s
      rw [gramSchmidt_def]
      simp only [Submodule.starProjection_singleton]
      rfl
    rw [heq]
    apply (finiteBorelSection_raw f n).sub
    apply finiteBorelSection_sum
    intro i hi
    have hg := ih i (Finset.mem_Iio.mp hi)
    apply hg.smul
    exact (hg.inner_measurable hgram (finiteBorelSection_raw f n)).div
      (Complex.continuous_ofReal.measurable.comp ((hg.norm_measurable hgram).pow_const 2))

theorem variableGramSchmidtNormed_finiteBorelSection (f : ∀ s, ℕ → E s)
    (hgram : ∀ i j, Measurable (fun s => inner ℂ (f s i) (f s j))) (n : ℕ) :
    FiniteBorelSection f (fun s => gramSchmidtNormed ℂ (f s) n) := by
  have hg := variableGramSchmidt_finiteBorelSection f hgram n
  exact hg.smul ((Complex.continuous_ofReal.measurable.comp (hg.norm_measurable hgram)).inv)

theorem FiniteBorelSection.map_linear {f : ∀ s, ℕ → E s}
    (T : ∀ s, E s →ₗ[ℂ] E s)
    (hT : ∀ n, FiniteBorelSection f (fun s => T s (f s n)))
    {v : ∀ s, E s} (hv : FiniteBorelSection f v) :
    FiniteBorelSection f (fun s => T s (v s)) := by
  obtain ⟨I, hI, j, c, hc, hv⟩ := hv
  letI := hI
  have heq : (fun s => T s (v s)) = fun s => ∑ i : I, c s i • T s (f s (j i)) := by
    funext s
    rw [hv s, map_sum]
    simp only [map_smul]
  rw [heq]
  exact finiteBorelSection_sum Finset.univ (fun i s => c s i • T s (f s (j i)))
    (fun i hi => (hT (j i)).smul (hc i))

theorem variableGramSchmidtNormed_norm_measurable (f : ∀ s, ℕ → E s)
    (hgram : ∀ i j, Measurable (fun s => inner ℂ (f s i) (f s j))) (n : ℕ) :
    Measurable (fun s => ‖gramSchmidtNormed ℂ (f s) n‖) :=
  (variableGramSchmidtNormed_finiteBorelSection f hgram n).norm_measurable hgram

theorem variableGramSchmidtNormed_nonzero_measurableSet (f : ∀ s, ℕ → E s)
    (hgram : ∀ i j, Measurable (fun s => inner ℂ (f s i) (f s j))) (n : ℕ) :
    MeasurableSet {s | gramSchmidtNormed ℂ (f s) n ≠ 0} := by
  have h := (variableGramSchmidtNormed_norm_measurable f hgram n) (measurableSet_singleton (0 : ℝ))
  simpa only [Set.preimage, Set.mem_singleton_iff, norm_eq_zero] using h.compl

set_option maxHeartbeats 800000 in
theorem variableGramSchmidtNormed_operator_inner_measurable (f : ∀ s, ℕ → E s)
    (hgram : ∀ i j, Measurable (fun s => inner ℂ (f s i) (f s j)))
    (T : ∀ s, E s →ₗ[ℂ] E s)
    (hT : ∀ n, FiniteBorelSection f (fun s => T s (f s n))) (i j : ℕ) :
    Measurable (fun s => inner ℂ (gramSchmidtNormed ℂ (f s) i)
      (T s (gramSchmidtNormed ℂ (f s) j))) :=
  (variableGramSchmidtNormed_finiteBorelSection f hgram i).inner_measurable hgram
    ((variableGramSchmidtNormed_finiteBorelSection f hgram j).map_linear T hT)



set_option maxHeartbeats 800000 in
theorem variableSelectedGramSchmidt_operator_inner_measurable (f : ∀ s, ℕ → E s)
    (hgram : ∀ i j, Measurable (fun s => inner ℂ (f s i) (f s j)))
    (hinf : ∀ s, {i | gramSchmidtNormed ℂ (f s) i ≠ 0}.Infinite)
    (T : ∀ s, E s →ₗ[ℂ] E s)
    (hT : ∀ n, FiniteBorelSection f (fun s => T s (f s n))) (i j : ℕ) :
    Measurable (fun s => inner ℂ (variableSelectedGramSchmidt f s i)
      (T s (variableSelectedGramSchmidt f s j))) := by
  classical
  have hI (n : ℕ) : Measurable (fun s => Nat.nth (fun k => gramSchmidtNormed ℂ (f s) k ≠ 0) n) :=
    measurable_nat_nth _ (variableGramSchmidtNormed_nonzero_measurableSet f hgram) hinf n
  have hm : Measurable (fun p : S × (ℕ × ℕ) =>
      inner ℂ (gramSchmidtNormed ℂ (f p.1) p.2.1)
        (T p.1 (gramSchmidtNormed ℂ (f p.1) p.2.2))) :=
    measurable_from_prod_countable_left (fun ij =>
      variableGramSchmidtNormed_operator_inner_measurable f hgram T hT ij.1 ij.2)
  exact hm.comp (measurable_id.prodMk ((hI i).prodMk (hI j)))

end MeasureUnitary

end

-- Preserved source skeleton: OperatorBlocks
section
/-!
Concrete block operators on a countable Hilbert sum, for the tuple coding.
All blocks are actual bounded operators; the estimates below justify the
operator-norm convergence of the weighted series in the manuscript.
-/

open ContinuousLinearMap
open scoped ENNReal

namespace OperatorCoding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]



















variable [CompleteSpace H]

theorem blockOperator_adjoint (i j : ℕ) (A : H →L[ℂ] H) :
    (blockOperator i j A).adjoint = blockOperator j i A.adjoint := by
  apply Eq.symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  rw [blockOperator_apply, blockOperator_apply, lp.inner_single_left, lp.inner_single_right]
  exact A.adjoint_inner_left _ _

end OperatorCoding

end

-- Preserved source skeleton: OperatorSeries
section
/-! The norm-convergent series of the countable unitary-tuple coding. -/

open ContinuousLinearMap

namespace OperatorCoding

set_option maxHeartbeats 1000000

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

















theorem unitaryCLM_norm_le (u : StrongUnitary H) : ‖(u : H →L[ℂ] H)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simpa using le_of_eq (u.norm_map x)



theorem tupleConnector_norm_le (u : ℕ → StrongUnitary H) (n : ℕ) :
    ‖tupleConnector u n‖ ≤ 2 := by
  unfold tupleConnector
  apply (norm_add_le (blockOperator (2 * n + 1) (2 * n + 2) (u n : H →L[ℂ] H))
    (blockOperator (2 * n + 2) (2 * n + 1) (u n : H →L[ℂ] H).adjoint)).trans
  have h₁ := (blockOperator_norm_le (2 * n + 1) (2 * n + 2) (u n : H →L[ℂ] H)).trans
    (unitaryCLM_norm_le (u n))
  have h₂ : ‖blockOperator (2 * n + 2) (2 * n + 1) (u n : H →L[ℂ] H).adjoint‖ ≤ 1 := by
    apply (blockOperator_norm_le _ _ _).trans
    simpa using unitaryCLM_norm_le (u n).symm
  linarith











theorem summable_tupleConnectors (u : ℕ → StrongUnitary H) :
    Summable (fun n => weightedOperator (1 / 16) n (tupleConnector u n)) :=
  summable_weightedOperator (tupleConnector_norm_le u) _



end OperatorCoding

end

-- Preserved source skeleton: OperatorAdjoints
section
/-! Self-adjointness and the 7/8 norm bound in the tuple coding. -/

open ContinuousLinearMap
open scoped ENNReal

namespace OperatorCoding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]



theorem identityBlock_star (i j : ℕ) : star (identityBlock (H := H) i j) = identityBlock j i := by
  simp only [identityBlock, ContinuousLinearMap.star_eq_adjoint, blockOperator_adjoint,
    ContinuousLinearMap.adjoint_id]

theorem starConnector_star (n : ℕ) : star (starConnector (H := H) n) = starConnector n := by
  simp [starConnector, star_add, identityBlock_star, add_comm]

theorem tupleConnector_star (u : ℕ → StrongUnitary H) (n : ℕ) :
    star (tupleConnector u n) = tupleConnector u n := by
  simp only [tupleConnector, star_add, ContinuousLinearMap.star_eq_adjoint,
    blockOperator_adjoint, ContinuousLinearMap.adjoint_adjoint, add_comm]

theorem weightedOperator_star (c : ℝ) (n : ℕ)
    (A : HilbertSum H →L[ℂ] HilbertSum H) :
    star (weightedOperator c n A) = weightedOperator c n (star A) := by
  simp [weightedOperator, star_smul]

theorem tupleDiagonal_star : star (tupleDiagonal (H := H)) = tupleDiagonal := by
  rw [tupleDiagonal, tsum_star]
  congr 1
  funext n
  rw [weightedOperator_star, identityBlock_star]

theorem tupleImaginaryPart_star (u : ℕ → StrongUnitary H) :
    star (tupleImaginaryPart u) = tupleImaginaryPart u := by
  unfold tupleImaginaryPart
  rw [star_add, tsum_star, tsum_star]
  congr 1 <;> congr 1 <;> funext n
  · rw [weightedOperator_star, starConnector_star]
  · rw [weightedOperator_star, tupleConnector_star]





end OperatorCoding

end

-- Preserved source skeleton: OperatorAmplification
section
/-! The direct sum of one unitary on every Hilbert summand. -/

namespace OperatorCoding

open scoped ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]



theorem amplifyUnitary_apply (W : StrongUnitary H) (x : HilbertSum H) (i : ℕ) :
    amplifyUnitary W x i = W (x i) := rfl



theorem amplifyUnitary_block_intertwines (W : StrongUnitary H) (i j : ℕ)
    (A B : H →L[ℂ] H) (hAB : ∀ x, W (A x) = B (W x)) (x : HilbertSum H) :
    amplifyUnitary W (blockOperator i j A x) = blockOperator i j B (amplifyUnitary W x) := by
  apply lp.ext
  funext k
  by_cases h : k = i
  · subst k
    simp [amplifyUnitary_apply, blockOperator_coordinate, hAB]
  · simp [amplifyUnitary_apply, blockOperator_coordinate, h]

end OperatorCoding

end

-- Preserved source skeleton: OperatorConjugation
section
/-! A unitary conjugacy of coded operators preserves the diagonal marker
and separately intertwines the self-adjoint tuple-coding component. -/

namespace OperatorCoding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem operatorUnitaryEquivalent_iff_conjugate (T S : H →L[ℂ] H) :
    OperatorUnitaryEquivalent T S ↔ ∃ Q : StrongUnitary H, Q.conjStarAlgEquiv T = S := by
  constructor
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, ?_⟩
    ext x
    simpa using hQ (Q.symm x)
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, fun x => ?_⟩
    have h := congrArg (fun A : H →L[ℂ] H => A (Q x)) hQ
    simpa using h



theorem operatorRealPart_conjugate (Q : StrongUnitary H) (T : H →L[ℂ] H) :
    Q.conjStarAlgEquiv (operatorRealPart T) = operatorRealPart (Q.conjStarAlgEquiv T) := by
  simp only [operatorRealPart, map_smul, map_add]
  exact congrArg (fun A : H →L[ℂ] H => (1 / 2 : ℂ) • (Q.conjStarAlgEquiv T + A))
    (Q.conjStarAlgEquiv.map_star' T)

theorem tupleCodedOperator_realPart (u : ℕ → StrongUnitary H) :
    operatorRealPart (tupleCodedOperator u) = tupleDiagonal := by
  simp only [operatorRealPart, tupleCodedOperator, star_add, star_smul, tupleDiagonal_star,
    tupleImaginaryPart_star, Complex.star_def, map_neg, Complex.conj_I]
  module

theorem codedOperator_conjugate_diagonal (u v : ℕ → StrongUnitary H)
    (Q : StrongUnitary (HilbertSum H))
    (hQ : Q.conjStarAlgEquiv (tupleCodedOperator u) = tupleCodedOperator v) :
    Q.conjStarAlgEquiv tupleDiagonal = tupleDiagonal := by
  calc
    Q.conjStarAlgEquiv tupleDiagonal =
        Q.conjStarAlgEquiv (operatorRealPart (tupleCodedOperator u)) := by
      rw [tupleCodedOperator_realPart]
    _ = operatorRealPart (Q.conjStarAlgEquiv (tupleCodedOperator u)) :=
      operatorRealPart_conjugate _ _
    _ = operatorRealPart (tupleCodedOperator v) := by rw [hQ]
    _ = tupleDiagonal := tupleCodedOperator_realPart v

theorem codedOperator_conjugate_imaginary (u v : ℕ → StrongUnitary H)
    (Q : StrongUnitary (HilbertSum H))
    (hQ : Q.conjStarAlgEquiv (tupleCodedOperator u) = tupleCodedOperator v) :
    Q.conjStarAlgEquiv (tupleImaginaryPart u) = tupleImaginaryPart v := by
  have hd := codedOperator_conjugate_diagonal u v Q hQ
  have hi : Complex.I • Q.conjStarAlgEquiv (tupleImaginaryPart u) =
      Complex.I • tupleImaginaryPart v := by
    apply add_left_cancel (a := tupleDiagonal)
    simpa only [tupleCodedOperator, map_add, map_smul, hd] using hQ
  exact (smul_right_injective (HilbertSum H →L[ℂ] HilbertSum H)
    (by simp : Complex.I ≠ 0)) hi

theorem codedOperator_commutes_diagonal (u v : ℕ → StrongUnitary H)
    (Q : StrongUnitary (HilbertSum H))
    (hQ : Q.conjStarAlgEquiv (tupleCodedOperator u) = tupleCodedOperator v) :
    ∀ x, Q (tupleDiagonal x) = tupleDiagonal (Q x) := by
  intro x
  have h := congrArg (fun T : HilbertSum H →L[ℂ] HilbertSum H => T (Q x))
    (codedOperator_conjugate_diagonal u v Q hQ)
  simpa using h

end OperatorCoding

end

-- Preserved source skeleton: OperatorEigenspaces
section
/-! The diagonal marker separates all countably many Hilbert summands. -/

namespace OperatorCoding

open scoped ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]



























theorem commutingDiagonal_coordinate (Q : StrongUnitary (HilbertSum H))
    (hQ : ∀ x, Q (tupleDiagonal x) = tupleDiagonal (Q x)) (x : HilbertSum H) (i : ℕ) :
    Q x i = diagonalRestriction Q i (x i) := by
  have hsum := lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ∞) x
  have hcoord := ((hsum.mapL (Q : HilbertSum H →L[ℂ] HilbertSum H)).mapL
    (lp.evalCLM ℂ (fun _ : ℕ => H) 2 i)).tsum_eq
  change (∑' j, Q (lp.single 2 j (x j)) i) = Q x i at hcoord
  rw [← hcoord, tsum_eq_single i]
  · rfl
  · intro j hji
    rw [commutingDiagonal_single Q hQ j]
    simp [lp.single_apply, Ne.symm hji]

end OperatorCoding

end

-- Preserved source skeleton: OperatorPreservation
section
/-! A simultaneous conjugacy of the tuple implements a conjugacy of the
single bounded operator by taking its direct sum on all summands. -/

namespace OperatorCoding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem unitaryConjugate_tsum (Q : StrongUnitary H) (f : ℕ → H →L[ℂ] H) :
    Q.conjStarAlgEquiv (∑' n, f n) = ∑' n, Q.conjStarAlgEquiv (f n) := by
  exact Q.toContinuousLinearEquiv.conjContinuousAlgEquiv.toContinuousLinearEquiv.map_tsum (f := f)

theorem amplifyUnitary_conjugates_block (W : StrongUnitary H) (i j : ℕ)
    (A B : H →L[ℂ] H) (hAB : ∀ x, W (A x) = B (W x)) :
    (amplifyUnitary W).conjStarAlgEquiv (blockOperator i j A) = blockOperator i j B := by
  apply ContinuousLinearMap.ext
  intro x
  simpa using amplifyUnitary_block_intertwines W i j A B hAB ((amplifyUnitary W).symm x)

theorem amplifyUnitary_conjugates_identityBlock (W : StrongUnitary H) (i j : ℕ) :
    (amplifyUnitary W).conjStarAlgEquiv (identityBlock i j) = identityBlock i j := by
  apply amplifyUnitary_conjugates_block
  intro x
  rfl

theorem amplifyUnitary_conjugates_starConnector (W : StrongUnitary H) (n : ℕ) :
    (amplifyUnitary W).conjStarAlgEquiv (starConnector n) = starConnector n := by
  simp only [starConnector, map_add, amplifyUnitary_conjugates_identityBlock]

theorem unitary_intertwines_inverse (W U V : StrongUnitary H)
    (h : ∀ x, W (U x) = V (W x)) : ∀ x, W (U.symm x) = V.symm (W x) := by
  intro x
  apply V.injective
  simpa using (h (U.symm x)).symm

theorem amplifyUnitary_conjugates_tupleConnector (W : StrongUnitary H)
    (u v : ℕ → StrongUnitary H) (h : ∀ n x, W (u n x) = v n (W x)) (n : ℕ) :
    (amplifyUnitary W).conjStarAlgEquiv (tupleConnector u n) = tupleConnector v n := by
  unfold tupleConnector
  rw [map_add]
  congr 1
  · exact amplifyUnitary_conjugates_block W _ _ _ _ (h n)
  · apply amplifyUnitary_conjugates_block
    intro x
    simpa using unitary_intertwines_inverse W (u n) (v n) (h n) x

theorem amplifyUnitary_conjugates_diagonal (W : StrongUnitary H) :
    (amplifyUnitary W).conjStarAlgEquiv tupleDiagonal = tupleDiagonal := by
  unfold tupleDiagonal
  rw [unitaryConjugate_tsum]
  apply tsum_congr
  intro n
  simp only [weightedOperator, map_smul, amplifyUnitary_conjugates_identityBlock]

theorem amplifyUnitary_conjugates_imaginary (W : StrongUnitary H)
    (u v : ℕ → StrongUnitary H) (h : ∀ n x, W (u n x) = v n (W x)) :
    (amplifyUnitary W).conjStarAlgEquiv (tupleImaginaryPart u) = tupleImaginaryPart v := by
  unfold tupleImaginaryPart
  rw [map_add, unitaryConjugate_tsum, unitaryConjugate_tsum]
  congr 1 <;> apply tsum_congr <;> intro n
  · simp only [weightedOperator, map_smul, amplifyUnitary_conjugates_starConnector]
  · simp only [weightedOperator, map_smul, amplifyUnitary_conjugates_tupleConnector W u v h]

theorem tupleCodedOperator_preserves (u v : ℕ → StrongUnitary H)
    (h : TupleConjugate u v) :
    OperatorUnitaryEquivalent (tupleCodedOperator u) (tupleCodedOperator v) := by
  obtain ⟨W, hW⟩ := h
  have hw : ∀ n x, W (u n x) = v n (W x) := by
    intro n x
    have hx := congrArg (fun U : StrongUnitary H => U (W x)) (hW n)
    simpa using hx
  apply (operatorUnitaryEquivalent_iff_conjugate _ _).mpr
  refine ⟨amplifyUnitary W, ?_⟩
  simp only [tupleCodedOperator, map_add, map_smul, amplifyUnitary_conjugates_diagonal,
    amplifyUnitary_conjugates_imaginary W u v hw]

end OperatorCoding

end

-- Preserved source skeleton: OperatorRecovery
section
/-! Recovery of one simultaneous intertwiner from a conjugacy of the coded
bounded operators.  The star-shaped identity edges force all diagonal
unitaries to coincide, and the remaining edges recover every input unitary. -/

namespace OperatorCoding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem positiveGeometric_coefficient_ne_zero (c : ℝ) (hc : c ≠ 0) (n : ℕ) :
    (((c * (1 / 2 : ℝ) ^ n : ℝ)) : ℂ) ≠ 0 := by
  apply Complex.ofReal_ne_zero.mpr
  exact mul_ne_zero hc (pow_ne_zero _ (by norm_num))

theorem conjugate_eq_intertwines (Q : StrongUnitary H) (T S : H →L[ℂ] H)
    (h : Q.conjStarAlgEquiv T = S) : ∀ x, Q (T x) = S (Q x) := by
  intro x
  have hx := congrArg (fun A : H →L[ℂ] H => A (Q x)) h
  simpa using hx

theorem coding_diagonalRestrictions_equal (u v : ℕ → StrongUnitary H)
    (Q : StrongUnitary (HilbertSum H))
    (hd : ∀ x, Q (tupleDiagonal x) = tupleDiagonal (Q x))
    (hb : ∀ x, Q (tupleImaginaryPart u x) = tupleImaginaryPart v (Q x))
    (j : ℕ) (x : H) : diagonalRestriction Q j x = diagonalRestriction Q 0 x := by
  cases j with
  | zero => rfl
  | succ j =>
    have h := congrArg (fun z : HilbertSum H => z 0) (hb (lp.single 2 (j + 1) x))
    dsimp only at h
    rw [commutingDiagonal_coordinate Q hd, tupleImaginaryPart_star_entry,
      commutingDiagonal_single Q hd, tupleImaginaryPart_star_entry,
      (diagonalRestriction Q 0).map_smul] at h
    exact ((smul_right_injective H
      (positiveGeometric_coefficient_ne_zero (1 / 32) (by norm_num) j)) h).symm

theorem coding_recovered_intertwiner (u v : ℕ → StrongUnitary H)
    (Q : StrongUnitary (HilbertSum H))
    (hd : ∀ x, Q (tupleDiagonal x) = tupleDiagonal (Q x))
    (hb : ∀ x, Q (tupleImaginaryPart u x) = tupleImaginaryPart v (Q x))
    (n : ℕ) (x : H) :
    diagonalRestriction Q 0 (u n x) = v n (diagonalRestriction Q 0 x) := by
  have h := congrArg (fun z : HilbertSum H => z (2 * n + 1))
    (hb (lp.single 2 (2 * n + 2) x))
  dsimp only at h
  rw [commutingDiagonal_coordinate Q hd, tupleImaginaryPart_tuple_entry,
    commutingDiagonal_single Q hd, tupleImaginaryPart_tuple_entry,
    (diagonalRestriction Q (2 * n + 1)).map_smul] at h
  rw [coding_diagonalRestrictions_equal u v Q hd hb (2 * n + 1),
    coding_diagonalRestrictions_equal u v Q hd hb (2 * n + 2)] at h
  exact (smul_right_injective H
    (positiveGeometric_coefficient_ne_zero (1 / 16) (by norm_num) n)) h

theorem tupleCodedOperator_reflects (u v : ℕ → StrongUnitary H)
    (h : OperatorUnitaryEquivalent (tupleCodedOperator u) (tupleCodedOperator v)) :
    TupleConjugate u v := by
  obtain ⟨Q, hQ⟩ := (operatorUnitaryEquivalent_iff_conjugate _ _).mp h
  have hd := codedOperator_commutes_diagonal u v Q hQ
  have hb := conjugate_eq_intertwines Q _ _ (codedOperator_conjugate_imaginary u v Q hQ)
  let W := diagonalBlockUnitary Q hd 0
  refine ⟨W, fun n => ?_⟩
  apply LinearIsometryEquiv.ext
  intro x
  have hx := coding_recovered_intertwiner u v Q hd hb n (W.symm x)
  change W (u n (W.symm x)) = v n (W (W.symm x)) at hx
  simpa using hx

end OperatorCoding

end

-- Preserved source skeleton: OperatorTupleCoding
section
/-!
The manuscript's explicit continuous reduction from simultaneous unitary
equivalence of countable tuples to unitary equivalence of a single operator.
The target is the actual countable Hilbert sum, with the strong operator
topology, and the resulting operators have norm at most 7/8.
-/

open ContinuousLinearMap

namespace OperatorCoding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem tupleConnector_continuous_apply (n : ℕ) (x : HilbertSum H) :
    Continuous (fun u : ℕ → StrongUnitary H => tupleConnector u n x) := by
  have h₁ : Continuous (fun u : ℕ → StrongUnitary H => u n (x (2 * n + 2))) :=
    (strongUnitary_continuous_eval _).comp (continuous_apply n)
  have h₂ : Continuous (fun u : ℕ → StrongUnitary H => (u n).symm (x (2 * n + 1))) :=
    (strongUnitary_continuous_eval _).comp (continuous_apply n).inv
  have hs₁ := (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => H) 2 (2 * n + 1)).continuous.comp h₁
  have hs₂ := (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => H) 2 (2 * n + 2)).continuous.comp h₂
  simpa only [tupleConnector, ContinuousLinearMap.add_apply, blockOperator_apply,
    LinearIsometryEquiv.adjoint_eq_symm, lp.singleContinuousLinearMap_apply] using hs₁.add hs₂

theorem weightedTupleConnector_continuous_apply (n : ℕ) (x : HilbertSum H) :
    Continuous (fun u : ℕ → StrongUnitary H => weightedOperator (1 / 16) n (tupleConnector u n) x) := by
  exact (tupleConnector_continuous_apply n x).const_smul
    ((((1 / 16 : ℝ) * (1 / 2 : ℝ) ^ n : ℝ) : ℂ))

theorem weightedTupleConnector_norm_bound (n : ℕ) (u : ℕ → StrongUnitary H) (x : HilbertSum H) :
    ‖weightedOperator (1 / 16) n (tupleConnector u n) x‖ ≤
      (‖x‖ / 8) * (1 / 2 : ℝ) ^ n := by
  have hb := weightedOperator_norm_le (tupleConnector_norm_le u) (1 / 16) n
  norm_num at hb
  calc
    ‖weightedOperator (1 / 16) n (tupleConnector u n) x‖ ≤
        ‖weightedOperator (1 / 16) n (tupleConnector u n)‖ * ‖x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ((1 / 8 : ℝ) * (1 / 2 : ℝ) ^ n) * ‖x‖ :=
      mul_le_mul_of_nonneg_right hb (norm_nonneg x)
    _ = (‖x‖ / 8) * (1 / 2 : ℝ) ^ n := by ring

theorem tupleImaginaryPart_continuous_apply (x : HilbertSum H) :
    Continuous (fun u : ℕ → StrongUnitary H => tupleImaginaryPart u x) := by
  have hsum : Continuous (fun u : ℕ → StrongUnitary H =>
      ∑' n, weightedOperator (1 / 16) n (tupleConnector u n) x) := by
    apply continuous_tsum (fun n => weightedTupleConnector_continuous_apply n x)
      ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (‖x‖ / 8))
    exact fun n u => weightedTupleConnector_norm_bound n u x
  have hconst : Continuous (fun _ : ℕ → StrongUnitary H =>
    (∑' n, weightedOperator (H := H) (1 / 32) n (starConnector n)) x) := continuous_const
  convert hconst.add hsum using 1
  funext u
  rw [tupleImaginaryPart, ContinuousLinearMap.add_apply]
  congr 1
  exact (ContinuousLinearMap.apply ℂ (HilbertSum H) x).map_tsum (summable_tupleConnectors u)

theorem tupleCodedOperator_continuous_apply (x : HilbertSum H) :
    Continuous (fun u : ℕ → StrongUnitary H => tupleCodedOperator u x) := by
  exact continuous_const.add ((tupleImaginaryPart_continuous_apply x).const_smul Complex.I)





theorem tupleCodedOperator_equivalent_iff (u v : ℕ → StrongUnitary H) :
    OperatorUnitaryEquivalent (tupleCodedOperator u) (tupleCodedOperator v) ↔
      TupleConjugate u v :=
  ⟨tupleCodedOperator_reflects u v, tupleCodedOperator_preserves u v⟩



end OperatorCoding

end

-- Preserved source skeleton: OperatorUnitaryBorel
section
/-! The strong topology on the unitary group is determined by countably
many dense vector evaluations. This identifies its Borel structure without
using operator-norm measurability in place of strong measurability. -/

open Filter Topology TopologicalSpace

namespace OperatorCoding

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [SeparableSpace H]



variable {H}







theorem strongUnitary_measurable_of_evaluations {X : Type*} [MeasurableSpace X]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (f : X → StrongUnitary H) (hf : ∀ x : H, Measurable (fun a => f a x)) :
    @Measurable X (StrongUnitary H) inferInstance (borel (StrongUnitary H)) f := by
  apply measurable_iff_comap_le.mpr
  change (borel (StrongUnitary H)).comap f ≤ (inferInstance : MeasurableSpace X)
  rw [strongUnitary_topology_eq_dense, borel_comap]
  rw [MeasurableSpace.comap_comp]
  have hb : (inferInstance : MeasurableSpace (ℕ → H)) = borel (ℕ → H) := BorelSpace.measurable_eq
  rw [← hb]
  exact measurable_iff_comap_le.mp (measurable_pi_iff.mpr (fun n => hf (denseSeq H n)))



end OperatorCoding

end

-- Preserved source skeleton: MeasureCantorBorel
section
/-! The genuine fixed-Hilbert Borel realization of the amplified
Cantor-cylinder multiplication representations. -/

open MeasureTheory Set Filter InnerProductSpace OperatorCoding
open scoped ENNReal

namespace MeasureUnitary

noncomputable section

attribute [local instance] _root_.MeasureUnitary.instMeasurableSpaceSubtypePreLpNatComplexMemAddSubgroupCanonicalHilbert_measureCantorBorel
local instance _root_.MeasureUnitary.instBorelSpaceSubtypePreLpNatComplexMemAddSubgroupCanonicalHilbert_measureCantorBorel : BorelSpace CanonicalHilbert := ⟨rfl⟩



theorem cantorFundamental_finiteBorelSection (k : CantorFundamentalIndex) :
    FiniteBorelSection (fun μ : ProbabilityMeasure CantorSpace => cantorFundamentalSequence (μ : Measure CantorSpace))
      (fun μ => cantorFundamentalVector (μ : Measure CantorSpace) k) := by
  obtain ⟨n, hn⟩ := cantorFundamentalEnumeration_surjective k
  simpa only [cantorFundamentalSequence, Function.comp_apply, hn] using
    finiteBorelSection_raw (fun μ : ProbabilityMeasure CantorSpace =>
      cantorFundamentalSequence (μ : Measure CantorSpace)) n

theorem cantorMultiplier_finiteBorelSection (r : CantorCylinderIndex) (n : ℕ) :
    FiniteBorelSection (fun μ : ProbabilityMeasure CantorSpace => cantorFundamentalSequence (μ : Measure CantorSpace))
      (fun μ => vectorCantorMultiplier (μ : Measure CantorSpace) r
        (cantorFundamentalSequence (μ : Measure CantorSpace) n)) := by
  simp only [cantorFundamentalSequence, Function.comp_apply, vectorCantorMultiplier_fundamental]
  exact (cantorFundamental_finiteBorelSection
    (cantorIntersectionIndex r (cantorFundamentalEnumeration n).1, (cantorFundamentalEnumeration n).2)).sub
    (cantorFundamental_finiteBorelSection
      (cantorIntersectionIndex (cantorComplementIndex r) (cantorFundamentalEnumeration n).1,
        (cantorFundamentalEnumeration n).2))

theorem cantorFiberBasis_apply (μ : ProbabilityMeasure CantorSpace) (n : ℕ) :
    cantorFiberBasis (μ : Measure CantorSpace) n = variableSelectedGramSchmidt
      (fun ν : ProbabilityMeasure CantorSpace => cantorFundamentalSequence (ν : Measure CantorSpace)) μ n := by
  unfold cantorFiberBasis
  rw [HilbertBasis.coe_mk]
  rfl

theorem measurable_cantorFiberBasis_multiplier_inner (r : CantorCylinderIndex) (i j : ℕ) :
    Measurable (fun μ : ProbabilityMeasure CantorSpace =>
      inner ℂ (cantorFiberBasis (μ : Measure CantorSpace) i)
        (vectorCantorMultiplier (μ : Measure CantorSpace) r (cantorFiberBasis (μ : Measure CantorSpace) j))) := by
  simp only [cantorFiberBasis_apply]
  exact variableSelectedGramSchmidt_operator_inner_measurable
    (fun μ : ProbabilityMeasure CantorSpace => cantorFundamentalSequence (μ : Measure CantorSpace))
    measurable_cantorFundamentalSequence_inner
    (fun μ => cantorFundamentalSequence_nonzero_infinite (μ : Measure CantorSpace))
    (fun μ => (vectorCantorMultiplier (μ : Measure CantorSpace) r).toLinearEquiv.toLinearMap)
    (cantorMultiplier_finiteBorelSection r) i j



theorem cantorCodedUnitary_coefficient (μ : ProbabilityMeasure CantorSpace) (r : CantorCylinderIndex)
    (i j : ℕ) :
    cantorCodedUnitary μ r (lp.single 2 j (1 : ℂ) : CanonicalHilbert) i =
      inner ℂ (cantorFiberBasis (μ : Measure CantorSpace) i)
        (vectorCantorMultiplier (μ : Measure CantorSpace) r (cantorFiberBasis (μ : Measure CantorSpace) j)) := by
  change (cantorFiberBasis (μ : Measure CantorSpace)).repr
    (vectorCantorMultiplier (μ : Measure CantorSpace) r
      ((cantorFiberBasis (μ : Measure CantorSpace)).repr.symm (lp.single 2 j (1 : ℂ)))) i = _
  rw [HilbertBasis.repr_symm_single, HilbertBasis.repr_apply_apply]

theorem measurable_cantorCodedUnitary_basis_apply (r : CantorCylinderIndex) (j : ℕ) :
    Measurable (fun μ : ProbabilityMeasure CantorSpace =>
      cantorCodedUnitary μ r (lp.single 2 j (1 : ℂ) : CanonicalHilbert)) := by
  apply canonicalHilbert_coordinates_measurableEmbedding.measurable_comp_iff.mp
  apply measurable_pi_iff.mpr
  intro i
  simpa only [Function.comp_apply, cantorCodedUnitary_coefficient] using
    measurable_cantorFiberBasis_multiplier_inner r i j

theorem strongUnitary_measurable_evaluations_of_basis {S : Type*} [MeasurableSpace S]
    (U : S → StrongUnitary CanonicalHilbert)
    (hU : ∀ j : ℕ, Measurable (fun s => U s (lp.single 2 j (1 : ℂ) : CanonicalHilbert)))
    (x : CanonicalHilbert) : Measurable (fun s => U s x) := by
  apply measurable_of_tendsto_metrizable
    (f := fun n s => ∑ j ∈ Finset.range n, (x j) • U s (lp.single 2 j (1 : ℂ) : CanonicalHilbert))
  · intro n
    exact (Finset.range n).measurable_sum (fun j hj => (hU j).const_smul (x j))
  · apply tendsto_pi_nhds.mpr
    intro s
    have hsum := ((U s).toContinuousLinearEquiv.toContinuousLinearMap.hasSum
      (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ∞) x)).tendsto_sum_nat
    convert hsum using 1
    funext n
    apply Finset.sum_congr rfl
    intro j hj
    have he : (lp.single 2 j (x j) : CanonicalHilbert) =
        (x j) • (lp.single 2 j (1 : ℂ) : CanonicalHilbert) := by
      simpa using (lp.single_smul (E := fun _ : ℕ => ℂ) 2 j (x j) (1 : ℂ))
    rw [he, map_smul]
    rfl

theorem cantorCodedUnitary_measurable (r : CantorCylinderIndex) :
    @Measurable (ProbabilityMeasure CantorSpace) (StrongUnitary CanonicalHilbert)
      inferInstance (borel _) (fun μ => cantorCodedUnitary μ r) :=
  strongUnitary_measurable_of_evaluations _
    (strongUnitary_measurable_evaluations_of_basis _ (measurable_cantorCodedUnitary_basis_apply r))

end

end MeasureUnitary

end

-- Preserved source skeleton: OperatorBireduction
section
/-!
The right-hand Borel bireducibility in Theorem 1.4:
all unitary representations of F∞ and all bounded operators on the same
fixed canonical separable infinite-dimensional Hilbert space.
-/

namespace OperatorCoding

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem fixedHilbertConjugation_equivalent_iff (E : H ≃ₗᵢ[ℂ] K) (T S : H →L[ℂ] H) :
    OperatorUnitaryEquivalent (E.conjStarAlgEquiv T) (E.conjStarAlgEquiv S) ↔
      OperatorUnitaryEquivalent T S := by
  constructor
  · rintro ⟨Q, hQ⟩
    refine ⟨(E.trans Q).trans E.symm, fun x => ?_⟩
    apply E.injective
    simpa using hQ (E x)
  · rintro ⟨Q, hQ⟩
    refine ⟨(E.symm.trans Q).trans E, fun x => ?_⟩
    simpa using congrArg E (hQ (E.symm x))



theorem canonicalTupleCodedOperator_equivalent_iff (u v : ℕ → StrongUnitary CanonicalHilbert) :
    OperatorUnitaryEquivalent (canonicalTupleCodedOperator u) (canonicalTupleCodedOperator v) ↔
      TupleConjugate u v :=
  (fixedHilbertConjugation_equivalent_iff _ _ _).trans (tupleCodedOperator_equivalent_iff u v)



theorem canonicalTupleCodedOperator_continuous :
    @Continuous (ℕ → StrongUnitary CanonicalHilbert) CanonicalOperator
      inferInstance operatorStrongTopology canonicalTupleCodedOperator := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro x
  exact canonicalHilbertSumEquiv.continuous.comp
    (tupleCodedOperator_continuous_apply (canonicalHilbertSumEquiv.symm x))











end OperatorCoding

end

-- Preserved source skeleton: RestrictedCompatibility
section
open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace MeasureEquivalenceRestrictedProduct



































theorem restrictedProductMeasure_compl :
    restrictedProductMeasure restrictedProductSpaceᶜ = 0 :=
  restrictedProductStages.limit_compl_union

theorem restrictedProductMeasure_base : restrictedProductMeasure (stageSet 0) = 1 := by
  have he := congrArg (fun μ : Measure RealSequences => μ univ)
    (restrictedProductMeasure_restrict 0)
  dsimp only at he
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, stageMeasure_zero,
    measure_univ] at he
  exact he







end MeasureEquivalenceRestrictedProduct

end

-- Preserved source skeleton: RestrictedDeparture
section
open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace MeasureEquivalenceRestrictedProduct








theorem one_le_exponentialDensity {t : ℝ} (ht : t ∈ baseInterval) :
    (1 : ℝ≥0∞) ≤ exponentialDensity t := by
  have hle : 1 ≤ Real.exp (-t) := Real.one_le_exp_iff.mpr (neg_nonneg.mpr ht.2)
  exact_mod_cast ENNReal.ofReal_le_ofReal hle



theorem volume_restrict_le_baseMeasure : (volume : Measure ℝ).restrict baseInterval ≤ baseMeasure := by
  unfold baseMeasure exponentialMeasure
  rw [restrict_withDensity (show MeasurableSet baseInterval from measurableSet_Icc)]
  conv_lhs => rw [← withDensity_one (μ := volume.restrict baseInterval)]
  apply withDensity_mono
  filter_upwards [ae_restrict_mem (show MeasurableSet baseInterval from measurableSet_Icc)] with t ht
  exact one_le_exponentialDensity ht



theorem departureSet_of_nonneg (u : ℝ) (hu : 0 ≤ u) (huL : u ≤ Real.log 2) :
    departureSet u = Ioc (-u) 0 := by
  ext t
  constructor
  · intro ht
    have htl : -Real.log 2 ≤ t := ht.1.1
    have htr : t ≤ 0 := ht.1.2
    have hbad : ¬ (-Real.log 2 ≤ t + u ∧ t + u ≤ 0) := ht.2
    constructor
    · by_contra h
      apply hbad
      constructor <;> linarith
    · exact htr
  · rintro ⟨htl, htr⟩
    constructor
    · constructor <;> linarith
    · intro hbad
      have := hbad.2
      linarith

theorem departureSet_of_nonpos (u : ℝ) (hu : u ≤ 0) (huL : -u ≤ Real.log 2) :
    departureSet u = Ico (-Real.log 2) (-Real.log 2 - u) := by
  ext t
  constructor
  · intro ht
    have htl : -Real.log 2 ≤ t := ht.1.1
    have htr : t ≤ 0 := ht.1.2
    have hbad : ¬ (-Real.log 2 ≤ t + u ∧ t + u ≤ 0) := ht.2
    constructor
    · exact htl
    · by_contra h
      apply hbad
      constructor <;> linarith
  · rintro ⟨htl, htr⟩
    constructor
    · constructor <;> linarith
    · intro hbad
      have := hbad.1
      linarith

theorem departureProbability_ge_abs_of_small (u : ℝ) (huL : |u| ≤ Real.log 2) :
    ENNReal.ofReal |u| ≤ departureProbability u := by
  change ENNReal.ofReal |u| ≤ baseMeasure (departureSet u)
  have hle := volume_restrict_le_baseMeasure (departureSet u)
  rw [Measure.restrict_apply (measurable_departureSet u),
    Set.inter_eq_left.mpr (show departureSet u ⊆ baseInterval from fun _ h => h.1)] at hle
  by_cases hu : 0 ≤ u
  · have he := departureSet_of_nonneg u hu (by simpa [abs_of_nonneg hu] using huL)
    rw [he, Real.volume_Ioc] at hle
    rw [he]
    simpa [abs_of_nonneg hu] using hle
  · have hu' : u ≤ 0 := le_of_not_ge hu
    have he := departureSet_of_nonpos u hu' (by simpa [abs_of_nonpos hu'] using huL)
    rw [he, Real.volume_Ico] at hle
    rw [he]
    simpa [abs_of_nonpos hu', show (-Real.log 2 - u) - -Real.log 2 = -u by ring] using hle

theorem departureProbability_eq_one_of_large (u : ℝ) (huL : Real.log 2 ≤ |u|) :
    departureProbability u = 1 := by
  have ha : ∀ᵐ t ∂baseMeasure, t ∈ departureSet u := by
    filter_upwards [ae_restrict_mem (show MeasurableSet baseInterval from measurableSet_Icc),
      Measure.ae_ne baseMeasure (-Real.log 2), Measure.ae_ne baseMeasure (0 : ℝ)] with t ht htl htr
    refine ⟨ht, ?_⟩
    intro hbad
    by_cases hu : 0 ≤ u
    · have hshift : Real.log 2 ≤ u := by simpa [abs_of_nonneg hu] using huL
      apply htl
      have h1 : -Real.log 2 ≤ t := ht.1
      have h2 : t + u ≤ 0 := hbad.2
      linarith
    · have hshift : Real.log 2 ≤ -u := by simpa [abs_of_nonpos (le_of_not_ge hu)] using huL
      apply htr
      have h1 : t ≤ 0 := ht.2
      have h2 : -Real.log 2 ≤ t + u := hbad.1
      linarith
  have hc : baseMeasure (departureSet u)ᶜ = 0 := ha
  have he := measure_add_measure_compl (μ := baseMeasure) (measurable_departureSet u)
  rw [hc, add_zero, measure_univ] at he
  exact he

theorem departureProbability_lower (u : ℝ) :
    ENNReal.ofReal (min 1 |u|) ≤ departureProbability u := by
  by_cases hu : |u| ≤ Real.log 2
  · exact (ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans
      (departureProbability_ge_abs_of_small u hu)
  · rw [departureProbability_eq_one_of_large u (le_of_not_ge hu)]
    simpa using ENNReal.ofReal_le_ofReal (min_le_left (1 : ℝ) |u|)

end MeasureEquivalenceRestrictedProduct

end

-- Preserved source skeleton: RestrictedSupport
section
open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace MeasureEquivalenceRestrictedProduct



theorem tsum_departureProbability_eq_top (h : ℕ → ℝ)
    (hh : ¬ Summable (fun n => |h n|)) : (∑' n, departureProbability (h n)) = ∞ := by
  by_contra hsum
  apply hh
  have hm : (∑' n, ENNReal.ofReal (min 1 |h n|)) ≠ ∞ :=
    ne_top_of_le_ne_top hsum (ENNReal.tsum_le_tsum (fun n => departureProbability_lower (h n)))
  have hreal : Summable (fun n => min 1 |h n|) :=
    (ENNReal.summable_toReal hm).congr (fun n =>
      ENNReal.toReal_ofReal (le_min zero_le_one (abs_nonneg (h n))))
  have hev : ∀ᶠ n in atTop, min 1 |h n| < 1 :=
    hreal.tendsto_atTop_zero.eventually (gt_mem_nhds zero_lt_one)
  apply hreal.congr_atTop
  filter_upwards [hev] with n hn
  exact min_eq_right ((min_lt_iff.mp hn).resolve_left (lt_irrefl _)).le









theorem ae_shift_not_mem_tailProbability (h : RealSequences)
    (hh : ¬ Summable (fun n => |h n|)) :
    ∀ᵐ x ∂tailProbability, x + h ∉ restrictedProductSpace := by
  let A : ℕ → Set RealSequences := fun n => {x | x n ∈ departureSet (h n)}
  have hAm (n : ℕ) : MeasurableSet (A n) :=
    (measurable_pi_apply n) (measurable_departureSet (h n))
  have hA (n : ℕ) : tailProbability (A n) = departureProbability (h n) := by
    have hm : tailProbability.map (fun x => x n) = baseMeasure :=
      Measure.infinitePi_map_eval (fun _ : ℕ => baseMeasure) n
    change tailProbability ((fun x : RealSequences => x n) ⁻¹' departureSet (h n)) = _
    rw [← Measure.map_apply (measurable_pi_apply n) (measurable_departureSet (h n)), hm]
    rfl
  have hi : ProbabilityTheory.iIndepSet A tailProbability := by
    apply (ProbabilityTheory.iIndepSet_iff_meas_biInter hAm).mpr
    intro s
    have he : (⋂ i ∈ s, A i) = Set.pi s (fun i => departureSet (h i)) := by
      ext x
      simp [A, Set.mem_pi]
    rw [he]
    change Measure.infinitePi (fun _ : ℕ => baseMeasure)
      (Set.pi s (fun i => departureSet (h i))) = _
    rw [Measure.infinitePi_pi (fun _ : ℕ => baseMeasure) (fun i _ => measurable_departureSet (h i))]
    exact Finset.prod_congr rfl (fun i _ => (hA i).symm)
  have hsum : (∑' n, tailProbability (A n)) = ∞ := by
    simp_rw [hA]
    exact tsum_departureProbability_eq_top h hh
  have hprob := ProbabilityTheory.measure_limsup_eq_one hAm hi hsum
  have hae : ∀ᵐ x ∂tailProbability, x ∈ limsup A atTop :=
    (mem_ae_iff_prob_eq_one (MeasurableSet.measurableSet_limsup hAm)).mpr hprob
  filter_upwards [hae] with x hx
  have hfreq := mem_limsup_iff_frequently_mem.mp hx
  intro hX
  obtain ⟨N, hN⟩ := mem_iUnion.mp hX
  have hev : ∀ᶠ k in atTop, x k + h k ∈ baseInterval := eventually_atTop.mpr ⟨N, hN⟩
  obtain ⟨k, hk, hki⟩ := (hfreq.and_eventually hev).exists
  exact hk.2 hki

theorem ae_shift_not_mem_stageMeasure (h : RealSequences)
    (hh : ¬ Summable (fun n => |h n|)) (n : ℕ) :
    ∀ᵐ x ∂stageMeasure n, x + h ∉ restrictedProductSpace := by
  let t : RealSequences := fun k => h (n + k)
  have ht : ¬ Summable (fun k => |t k|) := by
    intro hs
    apply hh
    have hs' : Summable (fun k => |h (k + n)|) := by simpa [t, Nat.add_comm] using hs
    exact Summable.comp_nat_add (f := fun k => |h k|) (k := n) hs'
  unfold stageMeasure
  apply (ae_map_iff (headTailEquiv n).symm.measurable.aemeasurable
    (((measurable_id.add_const h) measurable_restrictedProductSpace).compl)).mpr
  apply (Measure.ae_prod_iff_ae_ae
    ((((measurable_id.add_const h).comp (headTailEquiv n).symm.measurable)
      measurable_restrictedProductSpace).compl)).mpr
  apply ae_of_all
  intro head
  filter_upwards [ae_shift_not_mem_tailProbability t ht] with tail htail
  intro hX
  obtain ⟨M, hM⟩ := mem_iUnion.mp hX
  apply htail
  apply mem_iUnion.mpr
  refine ⟨M, ?_⟩
  intro r hr
  have hh' := hM (n + r) (by omega)
  simpa only [Function.comp_apply, id_eq, Pi.add_apply, headTailEquiv_symm_tail, t] using hh'

theorem map_shift_restrictedProductMeasure_null (h : RealSequences)
    (hh : ¬ Summable (fun n => |h n|)) :
    (restrictedProductMeasure.map (fun x => x + h)) restrictedProductSpace = 0 := by
  rw [Measure.map_apply (by fun_prop) measurable_restrictedProductSpace]
  change restrictedProductStages.limit {x | x + h ∈ restrictedProductSpace} = 0
  have hm : MeasurableSet {x : RealSequences | x + h ∈ restrictedProductSpace} :=
    (show Measurable (fun x : RealSequences => x + h) from by fun_prop)
      measurable_restrictedProductSpace
  rw [restrictedProductStages.limit_apply _ hm]
  apply ENNReal.iSup_eq_zero.mpr
  intro n
  have he := ae_iff.mp (ae_shift_not_mem_stageMeasure h hh n)
  simpa only [not_not] using he

theorem map_shift_mutuallySingular_of_not_summable (h : RealSequences)
    (hh : ¬ Summable (fun n => |h n|)) :
    restrictedProductMeasure.map (fun x => x + h) ⟂ₘ restrictedProductMeasure :=
  ⟨restrictedProductSpace, measurable_restrictedProductSpace,
    map_shift_restrictedProductMeasure_null h hh, restrictedProductMeasure_compl⟩

end MeasureEquivalenceRestrictedProduct

end

-- Preserved source skeleton: RestrictedAction
section
open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace MeasureEquivalenceRestrictedProduct



theorem rationalTotal_eq_sum (q : ℕ →₀ ℚ) :
    rationalTotal q = q.sum (fun _ a => a) := by
  exact Finsupp.liftAddHom_apply _ _







theorem summable_abs_rationalRealShift (q : ℕ →₀ ℚ) :
    Summable (fun k => |rationalRealShift q k|) := by
  exact summable_of_hasFiniteSupport
    (q.hasFiniteSupport.fun_comp (g := fun a : ℚ => |(a : ℝ)|) (by simp))

theorem tsum_rationalRealShift (q : ℕ →₀ ℚ) :
    (∑' k, rationalRealShift q k) = (rationalTotal q : ℝ) := by
  rw [tsum_eq_sum (s := q.support) (fun k hk => by
    change (q k : ℝ) = 0
    rw [Finsupp.notMem_support_iff.mp hk, Rat.cast_zero])]
  rw [rationalTotal_eq_sum]
  change (∑ k ∈ q.support, (q k : ℝ)) = ((∑ k ∈ q.support, q k : ℚ) : ℝ)
  norm_cast



theorem measurePreserving_rationalTranslation (q : rationalZeroSumGroup) :
    MeasurePreserving (rationalTranslation q) restrictedProductMeasure restrictedProductMeasure := by
  constructor
  · exact measurable_id.add_const _
  · have he := map_summable_restrictedProductMeasure (rationalRealShift q)
      (summable_abs_rationalRealShift q)
    rw [tsum_rationalRealShift, show rationalTotal (q : ℕ →₀ ℚ) = 0 from q.property,
      Rat.cast_zero, Real.exp_zero, ENNReal.ofReal_one, one_smul] at he
    exact he





end MeasureEquivalenceRestrictedProduct

end

-- Preserved source skeleton: RestrictedPhaseFamily
section
open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureEquivalenceRestrictedProduct MeasureEquivalenceSolenoid MeasureUnitary

















theorem character_add (i : CharacterIndex) (k l : CompactSequences) :
    character i (k + l) = character i k * character i l := by
  exact congrArg (fun z : Circle => (z : ℂ)) (AddCircle.toCircle_add _ _)



theorem sampleOrbit_measurable : Measurable sampleOrbit := by
  apply measurable_pi_lambda
  intro n
  exact ((measurable_pi_apply n).comp measurable_fst).add
    ((measurable_of_countable (fun q : rationalZeroSumGroup => rationalRealShift q n)).comp
      measurable_snd)



















end MeasureEquivalenceRestrictedPhase

end

-- Preserved source skeleton: RestrictedSpectralClass
section
open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureEquivalenceRestrictedProduct MeasureEquivalenceSolenoid

theorem characterFamily_injective :
    Function.Injective (fun k : CompactSequences => fun i : CharacterIndex => character i k) := by
  intro k l he
  funext n
  apply Subtype.ext
  funext q
  apply AddCircle.injective_toCircle (by norm_num : (1 : ℝ) ≠ 0)
  apply Subtype.ext
  exact congrFun he (n, q)





theorem orbitMeasure_apply {B : Set RealSequences} (hB : MeasurableSet B) :
    orbitMeasure B = ∑' q : rationalZeroSumGroup, tailProbability ((rationalTranslation q) ⁻¹' B) := by
  rw [orbitMeasure, Measure.map_apply sampleOrbit_measurable hB,
    sampleMeasure, Measure.prod_apply_symm (sampleOrbit_measurable hB), lintegral_count]
  rfl





theorem saturation_invariant (B : Set RealSequences) (q : rationalZeroSumGroup) :
    (rationalTranslation q) ⁻¹' saturation B = saturation B := by
  ext x
  simp only [saturation, mem_preimage, mem_iUnion]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r + q, (rationalTranslation_add r q x) ▸ hr⟩
  · rintro ⟨r, hr⟩
    refine ⟨r - q, ?_⟩
    rw [rationalTranslation_add, sub_add_cancel]
    exact hr

theorem orbitMeasure_null_iff {B : Set RealSequences} (hB : MeasurableSet B) :
    orbitMeasure B = 0 ↔ restrictedProductMeasure B = 0 := by
  rw [orbitMeasure_apply hB, ENNReal.tsum_eq_zero]
  constructor
  · intro hzero
    have hs : MeasurableSet (saturation B) := MeasurableSet.iUnion
      (fun q => (measurePreserving_rationalTranslation q).measurable hB)
    have hbase : tailProbability (saturation B) = 0 := by
      exact measure_iUnion_null hzero
    have hz : restrictedProductMeasure (saturation B) = 0 :=
      null_of_invariant_and_base_null (saturation B) hs
        (fun q => Filter.EventuallyEq.of_eq (saturation_invariant B q)) hbase
    apply measure_mono_null _ hz
    intro x hx
    apply mem_iUnion.mpr
    refine ⟨0, ?_⟩
    simpa [rationalTranslation] using hx
  · intro hz q
    have ht : restrictedProductMeasure ((rationalTranslation q) ⁻¹' B) = 0 := by
      rw [← Measure.map_apply (measurePreserving_rationalTranslation q).measurable hB,
        (measurePreserving_rationalTranslation q).map_eq, hz]
    have hbase : tailProbability ≪ restrictedProductMeasure := by
      rw [← stageMeasure_zero, ← restrictedProductMeasure_restrict 0]
      exact Measure.restrict_le_self.absolutelyContinuous
    exact hbase ht

theorem translated_spectral_null_iff (k : CompactSequences) (B : Set CompactSequences)
    (hB : MeasurableSet B) :
    sampleMeasure ((fun p : Sample => k + sequenceEmbedding (sampleOrbit p)) ⁻¹' B) = 0 ↔
      restrictedProductMeasure ((fun x : RealSequences => k + sequenceEmbedding x) ⁻¹' B) = 0 := by
  have hpre : MeasurableSet ((fun x : RealSequences => k + sequenceEmbedding x) ⁻¹' B) :=
    (continuous_const.add sequenceEmbedding_continuous).measurable hB
  rw [← orbitMeasure_null_iff hpre, orbitMeasure,
    Measure.map_apply sampleOrbit_measurable hpre]
  rfl

end MeasureEquivalenceRestrictedPhase

end

-- Preserved source skeleton: RestrictedCompactMeasure
section
open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureEquivalenceRestrictedProduct MeasureEquivalenceSolenoid







theorem compactMeasure_translate_real (h : RealSequences) :
    compactMeasure.map (fun z => z + sequenceEmbedding h) =
      (restrictedProductMeasure.map (fun x => x + h)).map sequenceEmbedding := by
  rw [compactMeasure, Measure.map_map (by fun_prop) sequenceEmbedding_continuous.measurable,
    Measure.map_map sequenceEmbedding_continuous.measurable (by fun_prop)]
  congr 1
  funext x
  exact (map_add sequenceEmbedding x h).symm



theorem compactMeasure_not_summable_singular (h : RealSequences)
    (hs : ¬ Summable (fun n => |h n|)) :
    compactMeasure.map (fun z => z + sequenceEmbedding h) ⟂ₘ compactMeasure := by
  rw [compactMeasure_translate_real]
  exact sequenceEmbedding_measurableEmbedding.mutuallySingular_map
    (map_shift_mutuallySingular_of_not_summable h hs)

theorem compactMeasure_outside_real_range_singular (k : CompactSequences)
    (hk : k ∉ range sequenceEmbedding) :
    compactMeasure.map (fun z => z + k) ⟂ₘ compactMeasure := by
  let R := range sequenceEmbedding
  have hR : MeasurableSet R := sequenceEmbedding_measurableEmbedding.measurableSet_range
  refine ⟨R, hR, ?_, ?_⟩
  · rw [Measure.map_apply (by fun_prop) hR, compactMeasure,
      Measure.map_apply sequenceEmbedding_continuous.measurable ((by fun_prop :
        Measurable (fun z : CompactSequences => z + k)) hR)]
    have he : sequenceEmbedding ⁻¹' ((fun z : CompactSequences => z + k) ⁻¹' R) = ∅ := by
      ext x
      simp only [mem_preimage, R, mem_range, mem_empty_iff_false, iff_false]
      rintro ⟨y, hy⟩
      apply hk
      refine ⟨y - x, ?_⟩
      rw [map_sub, hy, add_sub_cancel_left]
    rw [he, measure_empty]
  · rw [compactMeasure, Measure.map_apply sequenceEmbedding_continuous.measurable hR.compl]
    have he : sequenceEmbedding ⁻¹' Rᶜ = ∅ := by ext x; simp [R]
    rw [he, measure_empty]

theorem compactMeasure_outside_summable_singular (k : CompactSequences)
    (hk : k ∉ summableSubgroup) :
    compactMeasure.map (fun z => z + k) ⟂ₘ compactMeasure := by
  by_cases hR : k ∈ range sequenceEmbedding
  · obtain ⟨h, rfl⟩ := hR
    apply compactMeasure_not_summable_singular
    intro hs
    have hm : Memℓp h 1 := by
      apply (memℓp_gen_iff (by norm_num : (0 : ℝ) < (1 : ℝ≥0∞).toReal)).2
      simpa only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs] using hs
    exact hk ⟨⟨h, hm⟩, rfl⟩
  · exact compactMeasure_outside_real_range_singular k hR

end MeasureEquivalenceRestrictedPhase

end

-- Preserved source skeleton: RestrictedCompactAction
section
open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureEquivalenceRestrictedProduct MeasureEquivalenceSolenoid

theorem compactMeasure_base : compactMeasure (sequenceEmbedding '' stageSet 0) = 1 := by
  rw [compactMeasure, sequenceEmbedding_measurableEmbedding.map_apply,
    sequenceEmbedding_injective.preimage_image, restrictedProductMeasure_base]



theorem compactMeasure_ne_zero : compactMeasure ≠ 0 := by
  intro he
  have hh := compactMeasure_base
  simp [he] at hh











end MeasureEquivalenceRestrictedPhase

end

-- Preserved source skeleton: RestrictedInducedTuple
section
open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureEquivalenceRestrictedProduct MeasureEquivalenceSolenoid
open MeasureEquivalenceInducedCorners MeasureUnitary

theorem inducedFamilyPhase_coe (k : CompactSequences) (i : CharacterIndex) (u : InducedHilbert) :
    inducedFamilyPhase k i u =ᵐ[cornerMeasure (G := RationalGroup) restrictedProductMeasure (stageSet 0)]
      (fun p => ambientPhase k i (orbitPoint p) * u p) :=
  inducedPhaseUnitary_coe restrictedProductMeasure (stageSet 0) (ambientPhase k i)
    (ambientPhase_measurable _ _) (ambientPhase_norm _ _) u

theorem inducedFamilyPhase_factor (k : CompactSequences) (i : CharacterIndex) (u : InducedHilbert) :
    inducedFamilyPhase k i u = character i k • inducedFamilyPhase 0 i u := by
  apply Lp.ext
  filter_upwards [inducedFamilyPhase_coe k i u, inducedFamilyPhase_coe 0 i u,
    Lp.coeFn_smul (character i k) (inducedFamilyPhase 0 i u)] with p hp hp0 hsmul
  rw [hp, hsmul]
  change ambientPhase k i (orbitPoint p) * u p = character i k * (inducedFamilyPhase 0 i u) p
  rw [hp0]
  simp only [ambientPhase, zero_add, character_add, mul_assoc]

theorem inducedFamilyPhase_continuous (i : CharacterIndex) :
    Continuous (fun k : CompactSequences => inducedFamilyPhase k i) := by
  apply (OperatorCoding.strongUnitary_continuous_iff _).mpr
  intro u
  have he : (fun k : CompactSequences => inducedFamilyPhase k i u) =
      (fun k : CompactSequences => character i k • inducedFamilyPhase 0 i u) :=
    funext (fun k => inducedFamilyPhase_factor k i u)
  rw [he]
  exact (character_continuous i).smul continuous_const





theorem inducedGenerator_continuous (i : Generator) :
    Continuous (fun k : CompactSequences => inducedGenerator k i) := by
  cases i with
  | inl i => exact inducedFamilyPhase_continuous i
  | inr q => exact continuous_const



theorem generatorEnumeration_surjective : Function.Surjective generatorEnumeration :=
  Classical.choose_spec (exists_surjective_nat Generator)



theorem inducedTuple_continuous : Continuous inducedTuple :=
  continuous_pi (fun n => inducedGenerator_continuous (generatorEnumeration n))



theorem intertwines_generators_of_intertwines_tuple (k l : CompactSequences)
    (W : InducedHilbert ≃ₗᵢ[ℂ] InducedHilbert)
    (hW : ∀ n u, W (inducedTuple k n u) = inducedTuple l n (W u)) :
    (∀ i u, W (inducedFamilyPhase k i u) = inducedFamilyPhase l i (W u)) ∧
      (∀ q u, W (inducedFamilyShift q u) = inducedFamilyShift q (W u)) := by
  constructor
  · intro i u
    obtain ⟨n, hn⟩ := generatorEnumeration_surjective (Sum.inl i)
    have hh := hW n u
    simpa only [inducedTuple, inducedGenerator, hn, Sum.elim_inl] using hh
  · intro q u
    obtain ⟨n, hn⟩ := generatorEnumeration_surjective (Sum.inr q)
    have hh := hW n u
    simpa only [inducedTuple, inducedGenerator, hn, Sum.elim_inr] using hh

end MeasureEquivalenceRestrictedPhase

end

-- Preserved source skeleton: MeasureInducedOperatorCode
section
/-! Canonical fixed-space realization and bounded-operator coding of the
actual restricted-product induced representation family. -/

open MeasureTheory Set Filter Topology TopologicalSpace OperatorCoding InnerProductSpace
open scoped ENNReal

namespace MeasureEquivalenceRestrictedPhase

open MeasureEquivalenceRestrictedProduct MeasureEquivalenceSolenoid MeasureEquivalenceInducedCorners

noncomputable section



















attribute [local instance] _root_.MeasureEquivalenceRestrictedPhase.instMeasurableSpaceSubtypeAEEqFunProdRealSequencesRationalGroupComplexCornerMeasureRestrictedProductMeasureStageSetOfNatNatMemAddSubgroupInducedHilbert_measureInducedOperatorCode
attribute [local instance] _root_.MeasureEquivalenceRestrictedPhase.instBorelSpaceSubtypeAEEqFunProdRealSequencesRationalGroupComplexCornerMeasureRestrictedProductMeasureStageSetOfNatNatMemAddSubgroupInducedHilbert_measureInducedOperatorCode









theorem canonicalInducedTuple_continuous : Continuous canonicalInducedTuple := by
  apply continuous_pi
  intro n
  apply (strongUnitary_continuous_iff _).mpr
  intro x
  exact inducedCanonicalCoordinates.continuous.comp
    ((strongUnitary_continuous_eval (inducedCanonicalCoordinates.symm x)).comp
      ((continuous_apply n).comp inducedTuple_continuous))



theorem inducedCodedOperator_continuous :
    @Continuous CompactSequences CanonicalOperator inferInstance operatorStrongTopology inducedCodedOperator := by
  letI : TopologicalSpace CanonicalOperator := operatorStrongTopology
  exact canonicalTupleCodedOperator_continuous.comp canonicalInducedTuple_continuous



end

end MeasureEquivalenceRestrictedPhase

end

-- Preserved source skeleton: RestrictedInducedSpectral
section
open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureEquivalenceRestrictedProduct MeasureEquivalenceSolenoid
open MeasureEquivalenceInducedCorners



theorem groupTag_preserving : MeasurePreserving groupTagEquiv
    (Measure.count : Measure rationalZeroSumGroup) (Measure.count : Measure RationalGroup) := by
  refine ⟨groupTagEquiv.measurable, ?_⟩
  ext S hS
  rw [Measure.map_apply groupTagEquiv.measurable hS]
  have he : groupTagEquiv ⁻¹' S = groupTagEquiv.symm '' S := by
    ext x
    constructor
    · intro hx
      exact ⟨groupTagEquiv x, hx, groupTagEquiv.symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa only [mem_preimage, MeasurableEquiv.apply_symm_apply] using hy
  rw [he]
  exact Measure.count_injective_image groupTagEquiv.symm.injective S



theorem sampleTag_preserving : MeasurePreserving sampleTagEquiv sampleMeasure
    (cornerMeasure (G := RationalGroup) restrictedProductMeasure (stageSet 0)) := by
  rw [base_corner_measure_eq_base_product]
  exact (MeasurePreserving.id tailProbability).prod groupTag_preserving



theorem inducedObservable_measurable (k : CompactSequences) : Measurable (inducedObservable k) :=
  measurable_const.add (sequenceEmbedding_continuous.measurable.comp orbitPoint_measurable)



theorem induced_spectral_null_iff (k : CompactSequences) (B : Set CompactSequences)
    (hB : MeasurableSet B) :
    (cornerMeasure (G := RationalGroup) restrictedProductMeasure (stageSet 0))
        ((inducedObservable k) ⁻¹' B) = 0 ↔
      restrictedProductMeasure ((fun x : RealSequences => k + sequenceEmbedding x) ⁻¹' B) = 0 := by
  rw [← sampleTag_preserving.measure_preimage
    ((inducedObservable_measurable k) hB).nullMeasurableSet]
  exact translated_spectral_null_iff k B hB

theorem induced_push_spectral_null_iff (k : CompactSequences) (B : Set CompactSequences)
    (hB : MeasurableSet B) :
    ((cornerMeasure (G := RationalGroup) restrictedProductMeasure (stageSet 0)).map
      (inducedObservable k)) B = 0 ↔
      (compactMeasure.map (fun z => z + k)) B = 0 := by
  rw [Measure.map_apply (inducedObservable_measurable k) hB, induced_spectral_null_iff k B hB,
    compactMeasure, Measure.map_map (by fun_prop) sequenceEmbedding_continuous.measurable,
    Measure.map_apply ((by fun_prop : Measurable (fun z : CompactSequences => z + k)).comp
      sequenceEmbedding_continuous.measurable) hB]
  have he : (fun x : RealSequences => k + sequenceEmbedding x) =
      ((fun z : CompactSequences => z + k) ∘ sequenceEmbedding) := by
    funext x
    exact add_comm _ _
  rw [he]

end MeasureEquivalenceRestrictedPhase

end

-- Preserved source skeleton: SeparatingMultiplierIntertwining
section
open MeasureTheory Set Filter

noncomputable section

namespace MeasureEquivalenceRestrictedPhase





theorem characterContinuousMap_separates (x y : MeasureEquivalenceSolenoid.CompactSequences)
    (hxy : x ≠ y) : ∃ i, characterContinuousMap i x ≠ characterContinuousMap i y := by
  by_contra h
  apply hxy
  apply characterFamily_injective
  funext i
  exact not_ne_iff.mp (not_exists.mp h i)



end MeasureEquivalenceRestrictedPhase

end

-- Preserved source skeleton: RestrictedInducedReflection
section
open MeasureTheory MeasureTheory.Measure Filter Set
open scoped ENNReal

set_option maxHeartbeats 800000

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureEquivalenceRestrictedProduct MeasureEquivalenceSolenoid MeasureUnitary
open MeasureEquivalenceInducedCorners

attribute [local instance] _root_.MeasureEquivalenceRestrictedPhase.instMetricSpaceCompactSequences_restrictedInducedReflection



local instance _root_.MeasureEquivalenceRestrictedPhase.instSigmaFiniteProdRealSequencesRationalGroupInducedSampleMeasure : SigmaFinite inducedSampleMeasure := by
  change SigmaFinite (cornerMeasure (G := RationalGroup) restrictedProductMeasure (stageSet 0))
  rw [base_corner_measure_eq_base_product]
  infer_instance

theorem pullbackCharacter_eq_inducedPhase (k : CompactSequences) (i : CharacterIndex)
    (f : InducedHilbert) :
    pullbackMultiplierL2 inducedSampleMeasure (inducedObservable k) (inducedObservable_measurable k)
      (characterContinuousMap i) f = inducedFamilyPhase k i f := by
  apply Lp.ext
  filter_upwards [pullbackMultiplierL2_coe inducedSampleMeasure (inducedObservable k)
    (inducedObservable_measurable k) (characterContinuousMap i) f,
    inducedFamilyPhase_coe k i f] with p hleft hright
  rw [hleft, hright]
  rfl

theorem continuous_intertwining_of_inducedPhase_intertwining (k l : CompactSequences)
    (U : InducedHilbert ≃ₗᵢ[ℂ] InducedHilbert)
    (hU : ∀ i f, U (inducedFamilyPhase k i f) = inducedFamilyPhase l i (U f)) :
    ∀ (c : C(CompactSequences, ℂ)) (f : InducedHilbert),
      U (pullbackMultiplierL2 inducedSampleMeasure (inducedObservable k)
        (inducedObservable_measurable k) c f) =
        pullbackMultiplierL2 inducedSampleMeasure (inducedObservable l)
          (inducedObservable_measurable l) c (U f) := by
  apply continuous_intertwines_of_separating_family inducedSampleMeasure inducedSampleMeasure
    (inducedObservable k) (inducedObservable l)
    (inducedObservable_measurable k) (inducedObservable_measurable l)
    characterContinuousMap characterContinuousMap_separates U
  intro i f
  simpa only [pullbackCharacter_eq_inducedPhase] using hU i f



theorem inducedCompactShift_sample_class (k : CompactSequences) :
    inducedCompactShift k ≪ inducedSampleMeasure.map (inducedObservable k) ∧
      inducedSampleMeasure.map (inducedObservable k) ≪ inducedCompactShift k := by
  constructor
  · exact AbsolutelyContinuous.mk (fun B hB hz => (induced_push_spectral_null_iff k B hB).mp hz)
  · exact AbsolutelyContinuous.mk (fun B hB hz => (induced_push_spectral_null_iff k B hB).mpr hz)

theorem inducedCompactShift_intertwiner_equivalent (k l : CompactSequences)
    (U : InducedHilbert ≃ₗᵢ[ℂ] InducedHilbert)
    (hU : ∀ i f, U (inducedFamilyPhase k i f) = inducedFamilyPhase l i (U f)) :
    inducedCompactShift k ≪ inducedCompactShift l ∧ inducedCompactShift l ≪ inducedCompactShift k := by
  have h := push_measures_equivalent_of_intertwines_continuous inducedSampleMeasure inducedSampleMeasure
    (inducedObservable k) (inducedObservable l)
    (inducedObservable_measurable k) (inducedObservable_measurable l) U
    (continuous_intertwining_of_inducedPhase_intertwining k l U hU)
  have hk := inducedCompactShift_sample_class k
  have hl := inducedCompactShift_sample_class l
  exact ⟨hk.1.trans (h.1.trans hl.2), hl.1.trans (h.2.trans hk.2)⟩

theorem inducedPhase_intertwiner_difference_summable (k l : CompactSequences)
    (U : InducedHilbert ≃ₗᵢ[ℂ] InducedHilbert)
    (hU : ∀ i f, U (inducedFamilyPhase k i f) = inducedFamilyPhase l i (U f)) :
    k - l ∈ summableSubgroup := by
  have h := (inducedCompactShift_intertwiner_equivalent k l U hU).2.map
    (by fun_prop : Measurable (fun z : CompactSequences => z - l))
  have hleft : (inducedCompactShift l).map (fun z => z - l) = compactMeasure := by
    rw [inducedCompactShift, Measure.map_map (by fun_prop) (by fun_prop)]
    simp only [Function.comp_def, add_sub_cancel_right, Measure.map_id']
  have hright : (inducedCompactShift k).map (fun z => z - l) =
      compactMeasure.map (fun z => z + (k - l)) := by
    rw [inducedCompactShift, Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext z
    dsimp only [Function.comp_def]
    abel
  rw [hleft, hright] at h
  by_contra hk
  exact compactMeasure_ne_zero (Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular h
    (compactMeasure_outside_summable_singular (k - l) hk).symm)

theorem inducedTuple_intertwiner_difference_summable (k l : CompactSequences)
    (U : InducedHilbert ≃ₗᵢ[ℂ] InducedHilbert)
    (hU : ∀ n f, U (inducedTuple k n f) = inducedTuple l n (U f)) :
    k - l ∈ summableSubgroup :=
  inducedPhase_intertwiner_difference_summable k l U
    (intertwines_generators_of_intertwines_tuple k l U hU).1

end MeasureEquivalenceRestrictedPhase

end

-- Preserved source skeleton: MeasureInducedOperatorEquivalence
section
/-! Exact recovery and preservation for the actual induced family code. -/

open MeasureTheory OperatorCoding

namespace MeasureUnitary

variable {H K I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem tupleConjugate_iff_intertwiner (u v : I → StrongUnitary H) :
    TupleConjugate u v ↔ ∃ W : StrongUnitary H, ∀ i x, W (u i x) = v i (W x) := by
  constructor
  · rintro ⟨W, hW⟩
    refine ⟨W, fun i x => ?_⟩
    have h := congrArg (fun V : StrongUnitary H => V (W x)) (hW i)
    change W (u i (W.symm (W x))) = v i (W x) at h
    simpa using h
  · rintro ⟨W, hW⟩
    refine ⟨W, fun i => ?_⟩
    apply LinearIsometryEquiv.ext
    intro x
    simpa using hW i (W.symm x)

theorem transportedTuple_intertwiner_iff (E : H ≃ₗᵢ[ℂ] K) (u v : I → StrongUnitary H) :
    TupleConjugate (fun i => E.symm.trans ((u i).trans E)) (fun i => E.symm.trans ((v i).trans E)) ↔
      ∃ W : StrongUnitary H, ∀ i x, W (u i x) = v i (W x) := by
  rw [tupleConjugate_iff_intertwiner]
  constructor
  · rintro ⟨Q, hQ⟩
    refine ⟨E.trans (Q.trans E.symm), fun i x => ?_⟩
    simpa only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply] using
      congrArg E.symm (hQ i (E x))
  · rintro ⟨W, hW⟩
    refine ⟨E.symm.trans (W.trans E), fun i x => ?_⟩
    simpa only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply] using
      congrArg E (hW i (E.symm x))

end MeasureUnitary

namespace MeasureEquivalenceRestrictedPhase

open MeasureEquivalenceSolenoid

theorem inducedCodedOperator_equivalent_iff (k l : CompactSequences) :
    OperatorUnitaryEquivalent (inducedCodedOperator k) (inducedCodedOperator l) ↔
      ∃ W : StrongUnitary InducedHilbert, ∀ n u, W (inducedTuple k n u) = inducedTuple l n (W u) :=
  (canonicalTupleCodedOperator_equivalent_iff _ _).trans
    (MeasureUnitary.transportedTuple_intertwiner_iff inducedCanonicalCoordinates (inducedTuple k) (inducedTuple l))



theorem inducedCodedOperator_measurable :
    @Measurable CompactSequences CanonicalOperator inferInstance operatorBorel inducedCodedOperator := by
  letI : TopologicalSpace CanonicalOperator := operatorStrongTopology
  have hb : (inferInstance : MeasurableSpace CompactSequences) = borel CompactSequences :=
    BorelSpace.measurable_eq
  exact hb ▸ inducedCodedOperator_continuous.borel_measurable





end MeasureEquivalenceRestrictedPhase

end

-- Preserved source skeleton: MeasureOperatorReduction
section
/-! The actual forward Borel reduction from mutual absolute continuity
of Cantor probability measures to unitary equivalence of bounded operators. -/

open MeasureTheory Set OperatorCoding

namespace MeasureUnitary

noncomputable section



attribute [local instance] _root_.MeasureUnitary.instMeasurableSpaceStrongUnitarySubtypePreLpNatComplexMemAddSubgroupCanonicalHilbert_measureOperatorReduction
local instance _root_.MeasureUnitary.instBorelSpaceStrongUnitarySubtypePreLpNatComplexMemAddSubgroupCanonicalHilbert_measureOperatorReduction : BorelSpace (StrongUnitary CanonicalHilbert) := ⟨rfl⟩



theorem cantorCylinderEnumeration_surjective : Function.Surjective cantorCylinderEnumeration := by
  intro k
  obtain ⟨n, hn⟩ := cantorFundamentalEnumeration_surjective (k, 0)
  exact ⟨n, congrArg Prod.fst hn⟩



theorem cantorCodedTuple_measurable : Measurable cantorCodedTuple :=
  measurable_pi_iff.mpr (fun n => cantorCodedUnitary_measurable (cantorCylinderEnumeration n))

theorem cantorCodedUnitary_apply (μ : ProbabilityMeasure CantorSpace) (r : CantorCylinderIndex)
    (x : CanonicalHilbert) :
    cantorCodedUnitary μ r x = cantorFiberCoordinates (μ : Measure CantorSpace)
      (vectorCantorMultiplier (μ : Measure CantorSpace) r
        ((cantorFiberCoordinates (μ : Measure CantorSpace)).symm x)) := rfl

theorem cantorCodedTuple_equivalent_iff (μ ν : ProbabilityMeasure CantorSpace) :
    TupleConjugate (cantorCodedTuple μ) (cantorCodedTuple ν) ↔ MeasureEquivalent μ ν := by
  constructor
  · rintro ⟨W, hW⟩
    apply (amplifiedCantorMultiplierEquivalent_iff (μ : Measure CantorSpace) (ν : Measure CantorSpace)).mp
    let U : CantorFiber μ ≃ₗᵢ[ℂ] CantorFiber ν :=
      (cantorFiberCoordinates (μ : Measure CantorSpace)).trans
        (W.trans (cantorFiberCoordinates (ν : Measure CantorSpace)).symm)
    refine ⟨U, fun r f => ?_⟩
    obtain ⟨n, hn⟩ := cantorCylinderEnumeration_surjective r
    have heq := congrArg (fun V : StrongUnitary CanonicalHilbert =>
      V (W (cantorFiberCoordinates (μ : Measure CantorSpace) f))) (hW n)
    change W (cantorCodedUnitary μ (cantorCylinderEnumeration n)
      (W.symm (W (cantorFiberCoordinates (μ : Measure CantorSpace) f)))) =
        cantorCodedUnitary ν (cantorCylinderEnumeration n)
          (W (cantorFiberCoordinates (μ : Measure CantorSpace) f)) at heq
    rw [hn, W.symm_apply_apply, cantorCodedUnitary_apply, cantorCodedUnitary_apply,
      LinearIsometryEquiv.symm_apply_apply] at heq
    have hh := congrArg (cantorFiberCoordinates (ν : Measure CantorSpace)).symm heq
    simpa only [U, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply] using hh
  · intro h
    obtain ⟨U, hU⟩ := (amplifiedCantorMultiplierEquivalent_iff
      (μ : Measure CantorSpace) (ν : Measure CantorSpace)).mpr h
    let W : StrongUnitary CanonicalHilbert :=
      (cantorFiberCoordinates (μ : Measure CantorSpace)).symm.trans
        (U.trans (cantorFiberCoordinates (ν : Measure CantorSpace)))
    have hW (r : CantorCylinderIndex) (x : CanonicalHilbert) :
        W (cantorCodedUnitary μ r x) = cantorCodedUnitary ν r (W x) := by
      simpa only [W, cantorCodedUnitary_apply, LinearIsometryEquiv.trans_apply,
        LinearIsometryEquiv.symm_apply_apply] using
        congrArg (cantorFiberCoordinates (ν : Measure CantorSpace))
          (hU r ((cantorFiberCoordinates (μ : Measure CantorSpace)).symm x))
    refine ⟨W, fun n => ?_⟩
    apply LinearIsometryEquiv.ext
    intro x
    have hh := hW (cantorCylinderEnumeration n) (W.symm x)
    change W (cantorCodedTuple μ n (W.symm x)) = cantorCodedTuple ν n (W (W.symm x)) at hh
    simpa using hh



theorem measureCodedOperator_measurable :
    @Measurable (ProbabilityMeasure CantorSpace) CanonicalOperator inferInstance operatorBorel
      measureCodedOperator := by
  letI : TopologicalSpace CanonicalOperator := operatorStrongTopology
  have hb : (inferInstance : MeasurableSpace (ℕ → StrongUnitary CanonicalHilbert)) =
      borel (ℕ → StrongUnitary CanonicalHilbert) := BorelSpace.measurable_eq
  exact canonicalTupleCodedOperator_continuous.borel_measurable.comp (hb ▸ cantorCodedTuple_measurable)

theorem measureCodedOperator_equivalent_iff (μ ν : ProbabilityMeasure CantorSpace) :
    OperatorUnitaryEquivalent (measureCodedOperator μ) (measureCodedOperator ν) ↔ MeasureEquivalent μ ν :=
  (canonicalTupleCodedOperator_equivalent_iff _ _).trans (cantorCodedTuple_equivalent_iff μ ν)



theorem measureEquivalence_borelReduce_boundedOperators :
    BorelReducesWith (inferInstance : MeasurableSpace (ProbabilityMeasure CantorSpace)) operatorBorel
      MeasureEquivalent OperatorUnitaryEquivalent :=
  ⟨measureCodedOperator, measureCodedOperator_measurable, fun μ ν =>
    (measureCodedOperator_equivalent_iff μ ν).symm⟩

end

end MeasureUnitary

end

-- Preserved source skeleton: RestrictedTranslatedCorner
section
/-! The exact translated finite corner and the measure-preserving map
to the scalar multiple dictated by the restricted-product modulus. -/

open MeasureTheory Filter Set
open scoped ENNReal NNReal

set_option maxHeartbeats 1000000

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureUnitary MeasureEquivalenceSolenoid MeasureEquivalenceRestrictedProduct
  MeasureEquivalenceInducedCorners MeasureEquivalenceEquidecomposition























theorem translatedCornerPullback_coe (h : RealSequences) (hs : Summable (fun n => |h n|))
    (f : Lp ℂ 2 (translationScale h • cornerMeasure (G := RationalGroup) restrictedProductMeasure (stageSet 0))) :
    translatedCornerPullback h hs f =ᵐ[cornerMeasure (G := RationalGroup) restrictedProductMeasure (translatedCorner h)]
      fun p => f (translatedCornerEquiv h p) :=
  Lp.coeFn_compMeasurePreserving f (translatedCorner_preserving h hs)

end MeasureEquivalenceRestrictedPhase

end

-- Preserved source skeleton: ScalarMeasureNormalization
section
open MeasureTheory Filter
open scoped ENNReal NNReal

noncomputable section

namespace MeasureUnitary

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]







theorem scalar_rnWeight (c : ℝ≥0) :
    rnWeight (c • μ) μ =ᵐ[μ] fun _ => Real.sqrt (c : ℝ) := by
  filter_upwards [Measure.rnDeriv_smul_left' μ μ c, μ.rnDeriv_self] with x hx hself
  unfold rnWeight
  rw [hx]
  change Real.sqrt (((c : ℝ≥0∞) * μ.rnDeriv μ x).toReal) = _
  rw [hself]
  simp

theorem scalarMeasureEquiv_coe (c : ℝ≥0) (hc : c ≠ 0) (f : Lp ℂ 2 (c • μ)) :
    scalarMeasureEquiv μ c hc f =ᵐ[μ] fun x => Real.sqrt (c : ℝ) • f x := by
  change rnWeightedMap (c • μ) μ (scalar_smul_absolutelyContinuous μ c)
    (scalar_absolutelyContinuous_smul μ c hc) f =ᵐ[μ] _
  filter_upwards [rnWeightedMap_coe (c • μ) μ (scalar_smul_absolutelyContinuous μ c)
    (scalar_absolutelyContinuous_smul μ c hc) f, scalar_rnWeight μ c] with x hx hw
  rw [hx, hw]

theorem scalarMeasureEquiv_symm_coe (c : ℝ≥0) (hc : c ≠ 0) (f : Lp ℂ 2 μ) :
    (scalarMeasureEquiv μ c hc).symm f =ᵐ[c • μ]
      fun x => (Real.sqrt (c : ℝ))⁻¹ • f x := by
  have hcpos : 0 < (c : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hc)
  have hsqrt : Real.sqrt (c : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hcpos)
  have he := scalarMeasureEquiv_coe μ c hc ((scalarMeasureEquiv μ c hc).symm f)
  simp only [LinearIsometryEquiv.apply_symm_apply] at he
  refine Measure.ae_smul_measure ?_ c
  filter_upwards [he] with x hx
  have hh := congrArg (fun z : ℂ => (Real.sqrt (c : ℝ))⁻¹ • z) hx
  simpa only [smul_smul, inv_mul_cancel₀ hsqrt, one_smul] using hh.symm

end MeasureUnitary

end

-- Preserved source skeleton: RestrictedFullReflection
section
/-! Exact reflection of the zero-sum subgroup by the actual induced
unitary tuple. The normalization, trace comparison and summability
reflection are all constructed in the imported checked developments. -/

open MeasureTheory Filter Set
open scoped ENNReal NNReal

set_option maxHeartbeats 1500000

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureUnitary MeasureEquivalenceSolenoid MeasureEquivalenceRestrictedProduct
  MeasureEquivalenceInducedCorners

attribute [local instance] _root_.MeasureEquivalenceRestrictedPhase.instSigmaFiniteProdRealSequencesRationalGroupCornerMeasureRestrictedProductMeasureStageSetOfNatNat_restrictedFullReflection



theorem normalizedTranslation_coe (h : RealSequences) (hs : Summable (fun n => |h n|))
    (u : InducedHilbert) :
    normalizedTranslation h hs u =ᵐ[cornerMeasure (G := RationalGroup) restrictedProductMeasure (translatedCorner h)]
      fun p => (Real.sqrt (translationScale h : ℝ))⁻¹ • u (translatedCornerEquiv h p) := by
  filter_upwards [translatedCornerPullback_coe h hs
      ((scalarMeasureEquiv (cornerMeasure (G := RationalGroup) restrictedProductMeasure (stageSet 0))
        (translationScale h) (translationScale_ne_zero h)).symm u),
    (translatedCorner_preserving h hs).quasiMeasurePreserving.ae
      (scalarMeasureEquiv_symm_coe
        (cornerMeasure (G := RationalGroup) restrictedProductMeasure (stageSet 0))
          (translationScale h) (translationScale_ne_zero h) u)] with p hp hscl
  exact hp.trans hscl

theorem inducedTuple_intertwiner_difference_zeroSum (k l : CompactSequences)
    (W : InducedHilbert ≃ₗᵢ[ℂ] InducedHilbert)
    (hW : ∀ n u, W (inducedTuple k n u) = inducedTuple l n (W u)) :
    k - l ∈ zeroSumSubgroup := by
  have hsum := inducedTuple_intertwiner_difference_summable k l W hW
  have hlk : l - k ∈ summableSubgroup := by
    simpa only [neg_sub] using summableSubgroup.neg_mem hsum
  obtain ⟨h, he⟩ := hlk
  have hs : Summable (fun n => |h n|) := by
    simpa only [ENNReal.toReal_one, Real.rpow_one, Real.norm_eq_abs] using
      (lp.memℓp h).summable (by norm_num : (0 : ℝ) < (1 : ℝ≥0∞).toReal)
  have he' : k + sequenceEmbedding (h : RealSequences) = l := by
    change k + l1Embedding h = l
    rw [he]
    abel
  have hzero := total_eq_zero_of_normalized_intertwiner (h : RealSequences) hs k l he' W hW
    (normalizedTranslation (h : RealSequences) hs) (Real.sqrt (translationScale (h : RealSequences) : ℝ))⁻¹
    (normalizedTranslation_coe (h : RealSequences) hs)
  have hH : l - k ∈ zeroSumSubgroup := by
    rw [← he]
    exact (l1Embedding_mem_zeroSumSubgroup h).mpr hzero
  simpa only [neg_sub] using zeroSumSubgroup.neg_mem hH

theorem inducedTuple_intertwiner_iff_zeroSum (k l : CompactSequences) :
    (∃ W : InducedHilbert ≃ₗᵢ[ℂ] InducedHilbert,
      ∀ n u, W (inducedTuple k n u) = inducedTuple l n (W u)) ↔
        k - l ∈ zeroSumSubgroup := by
  constructor
  · rintro ⟨W, hW⟩
    exact inducedTuple_intertwiner_difference_zeroSum k l W hW
  · intro hkl
    apply exists_inducedTuple_intertwiner_of_zeroSum k l
    simpa only [neg_sub] using zeroSumSubgroup.neg_mem hkl

end MeasureEquivalenceRestrictedPhase

end

-- Preserved source skeleton: OperatorStrictSeparation
section
/-! Unconditional strict separation of measure equivalence from unitary
equivalence of all bounded operators, via the concrete compact zero-sum
quotient and the actual continuous bounded-operator family. -/

open MeasureTheory OperatorCoding

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureEquivalenceSolenoid

theorem inducedCodedOperator_equivalent_iff_zeroSum (k l : CompactSequences) :
    OperatorUnitaryEquivalent (inducedCodedOperator k) (inducedCodedOperator l) ↔
      k - l ∈ zeroSumSubgroup :=
  (inducedCodedOperator_equivalent_iff k l).trans (inducedTuple_intertwiner_iff_zeroSum k l)



end MeasureEquivalenceRestrictedPhase

namespace OperatorCoding

open MeasureUnitary MeasureEquivalenceRestrictedPhase MeasureEquivalenceSolenoid
  MeasureEquivalenceRigidity MeasureEquivalenceResearch

theorem boundedOperators_not_borelReduce_measureEquivalence :
    ¬ BorelReducesWith operatorBorel (inferInstance : MeasurableSpace (ProbabilityMeasure Cantor))
      OperatorUnitaryEquivalent MeasureEquivalent := by
  rintro ⟨f, hf, hred⟩
  apply zeroSum_not_reducible_to_measure_equivalence
  refine ⟨f ∘ inducedCodedOperator, hf.comp inducedCodedOperator_measurable, ?_⟩
  intro k l
  exact (hred (inducedCodedOperator k) (inducedCodedOperator l)).symm.trans
    (inducedCodedOperator_equivalent_iff_zeroSum k l)







end OperatorCoding

end

/-! Unconditional strict separation of measure equivalence from unitary
equivalence of all bounded operators, via the concrete compact zero-sum
quotient and the actual continuous bounded-operator family. -/
open MeasureTheory OperatorCoding
namespace OperatorCoding
end OperatorCoding
open OperatorCoding
open MeasureUnitary MeasureEquivalenceRestrictedPhase MeasureEquivalenceSolenoid
  MeasureEquivalenceRigidity MeasureEquivalenceResearch

theorem solution : Theorem13 :=
  ⟨measureEquivalence_borelReduce_boundedOperators,
    boundedOperators_not_borelReduce_measureEquivalence⟩
