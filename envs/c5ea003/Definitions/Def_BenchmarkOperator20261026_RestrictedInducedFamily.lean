-- Prove2me | Definitions.Def_BenchmarkOperator20261026_RestrictedInducedFamily
-- name    : BenchmarkOperator20261026_RestrictedInducedFamily
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:43:40.957798+00:00
-- url     : https://prove2.me/theorems/39e5d0ee-d8f0-48ae-a5b6-93e9c87f52a7
-- title:
--   Restricted Induced Family
-- statement:
--   Defines the rational acting group and its measurable-action instances, the ambient character phases, the induced $L^2$ space, and its phase and shift unitaries. The retained phase bounds and base-corner product identity justify this concrete operator family.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization RestrictedInducedFamily.lean, lines 14–67; source SHA-256 cc00712984e9d68f5e576a2b8c05570dc96be35bea1d364f97fa893739b153fd. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_InducedCornerTransport
import Definitions.Def_BenchmarkOperator20261026_InducedCornerUnitary
import Definitions.Def_BenchmarkOperator20261026_OperatorFreeGroup
import Definitions.Def_BenchmarkOperator20261026_OperatorStrongUnitary
import Definitions.Def_BenchmarkOperator20261026_RestrictedAction
import Definitions.Def_BenchmarkOperator20261026_RestrictedCompactMeasure
import Definitions.Def_BenchmarkOperator20261026_RestrictedCompatibility
import Definitions.Def_BenchmarkOperator20261026_RestrictedDensity
import Definitions.Def_BenchmarkOperator20261026_RestrictedFiniteModulus
import Definitions.Def_BenchmarkOperator20261026_RestrictedPhaseFamily
import Definitions.Def_BenchmarkOperator20261026_RestrictedProduct
import Definitions.Def_BenchmarkOperator20261026_RestrictedSpectralClass
import Definitions.Def_BenchmarkOperator20261026_RestrictedStages
import Definitions.Def_BenchmarkOperator20261026_SolenoidGroups
import Definitions.Def_BenchmarkOperator20261026_SumFiberCoordinates
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Set.Lattice
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Measure.MutuallySingular
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Polish
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

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureEquivalenceRestrictedProduct MeasureEquivalenceSolenoid
open MeasureEquivalenceInducedCorners MeasureEquivalenceEquidecomposition

abbrev RationalGroup := Multiplicative rationalZeroSumGroup

instance _root_.MeasureEquivalenceRestrictedPhase.instCountableRationalGroup : Countable RationalGroup :=
  (show Function.Injective (Multiplicative.toAdd : RationalGroup → rationalZeroSumGroup) from
    fun _ _ h => congrArg Multiplicative.ofAdd h).countable
instance _root_.MeasureEquivalenceRestrictedPhase.instMeasurableSpaceRationalGroup : MeasurableSpace RationalGroup := ⊤
instance _root_.MeasureEquivalenceRestrictedPhase.instMeasurableSingletonClassRationalGroup : MeasurableSingletonClass RationalGroup := ⟨fun _ => trivial⟩

instance _root_.MeasureEquivalenceRestrictedPhase.instMulActionRationalGroupRealSequences : MulAction RationalGroup RealSequences where
  smul q x := rationalTranslation (Multiplicative.toAdd q) x
  one_smul x := by
    change x + rationalRealShift (0 : ℕ →₀ ℚ) = x
    rw [map_zero, add_zero]
  mul_smul q r x := (rationalTranslation_add _ _ _).symm

instance _root_.MeasureEquivalenceRestrictedPhase.instMeasurableConstSMulRationalGroupRealSequences : MeasurableConstSMul RationalGroup RealSequences :=
  ⟨fun q => measurable_id.add_const _⟩





def ambientPhase (k : CompactSequences) (i : CharacterIndex) (x : RealSequences) : ℂ :=
  character i (k + sequenceEmbedding x)

theorem ambientPhase_measurable (k : CompactSequences) (i : CharacterIndex) :
    Measurable (ambientPhase k i) :=
  (character_continuous i).measurable.comp
    (measurable_const.add sequenceEmbedding_continuous.measurable)

theorem ambientPhase_norm (k : CompactSequences) (i : CharacterIndex) (x : RealSequences) :
    ‖ambientPhase k i x‖ = 1 := character_norm _ _

abbrev InducedHilbert :=
  Lp ℂ 2 (cornerMeasure (G := RationalGroup) restrictedProductMeasure (stageSet 0))

def inducedFamilyPhase (k : CompactSequences) (i : CharacterIndex) :
    InducedHilbert ≃ₗᵢ[ℂ] InducedHilbert :=
  inducedPhaseUnitary restrictedProductMeasure (stageSet 0) (ambientPhase k i)
    (ambientPhase_measurable k i) (ambientPhase_norm k i)

def inducedFamilyShift (q : RationalGroup) : InducedHilbert ≃ₗᵢ[ℂ] InducedHilbert :=
  inducedShiftUnitary restrictedProductMeasure (stageSet 0) q

theorem base_corner_measure_eq_base_product :
    cornerMeasure (G := RationalGroup) restrictedProductMeasure (stageSet 0) =
      tailProbability.prod (Measure.count : Measure RationalGroup) := by
  rw [cornerMeasure, restrictedProductMeasure_restrict 0, stageMeasure_zero]



end MeasureEquivalenceRestrictedPhase


