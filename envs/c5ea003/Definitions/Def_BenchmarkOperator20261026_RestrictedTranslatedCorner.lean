-- Prove2me | Definitions.Def_BenchmarkOperator20261026_RestrictedTranslatedCorner
-- name    : BenchmarkOperator20261026_RestrictedTranslatedCorner
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:49:54.409229+00:00
-- url     : https://prove2.me/theorems/e63d48a9-362d-4317-8a1d-6afcf7c4b5f4
-- title:
--   Restricted Translated Corner
-- statement:
--   Defines the translated distinguished corner, its exponential scaling factor, the corner translation equivalence and its unitary pullback. The retained preservation and nonzero-scaling facts justify these constructions. Exact phase covariance and mass reflection are later theorems.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization RestrictedTranslatedCorner.lean, lines 18–104; source SHA-256 ac39d78690d8e55bdc1bc33a4bde0624d5dd1ad42d4243c680a7abfcd827da62. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_HilbertSequenceTopology
import Definitions.Def_BenchmarkOperator20261026_InducedCornerTransport
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorDenseFamily
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorTuple
import Definitions.Def_BenchmarkOperator20261026_MeasureL2Constants
import Definitions.Def_BenchmarkOperator20261026_OperatorFreeGroup
import Definitions.Def_BenchmarkOperator20261026_OperatorStrongUnitary
import Definitions.Def_BenchmarkOperator20261026_PiecewiseMeasureTransport
import Definitions.Def_BenchmarkOperator20261026_RestrictedCompactMeasure
import Definitions.Def_BenchmarkOperator20261026_RestrictedCompatibility
import Definitions.Def_BenchmarkOperator20261026_RestrictedDensity
import Definitions.Def_BenchmarkOperator20261026_RestrictedFiniteModulus
import Definitions.Def_BenchmarkOperator20261026_RestrictedInducedFamily
import Definitions.Def_BenchmarkOperator20261026_RestrictedModulus
import Definitions.Def_BenchmarkOperator20261026_RestrictedPhaseFamily
import Definitions.Def_BenchmarkOperator20261026_RestrictedProduct
import Definitions.Def_BenchmarkOperator20261026_RestrictedStages
import Definitions.Def_BenchmarkOperator20261026_SolenoidGroups
import Definitions.Def_BenchmarkOperator20261026_SumFiberCoordinates
import Definitions.Def_BenchmarkOperator20261026_VectorSpectralState
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Set.Lattice
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
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

/-! The exact translated finite corner and the measure-preserving map
to the scalar multiple dictated by the restricted-product modulus. -/

open MeasureTheory Filter Set
open scoped ENNReal NNReal

set_option maxHeartbeats 1000000

noncomputable section

namespace MeasureEquivalenceRestrictedPhase

open MeasureUnitary MeasureEquivalenceSolenoid MeasureEquivalenceRestrictedProduct
  MeasureEquivalenceInducedCorners MeasureEquivalenceEquidecomposition

def translationScale (h : RealSequences) : ℝ≥0 :=
  ⟨Real.exp (∑' n, h n), (Real.exp_pos _).le⟩

theorem translationScale_ne_zero (h : RealSequences) : translationScale h ≠ 0 := by
  intro hc
  have he := congrArg (fun c : ℝ≥0 => (c : ℝ)) hc
  exact (Real.exp_pos (∑' n, h n)).ne' he

def translatedCorner (h : RealSequences) : Set RealSequences :=
  (fun x : RealSequences => x + h) ⁻¹' stageSet 0









def translatedCornerEquiv (h : RealSequences) :
    (RealSequences × RationalGroup) ≃ᵐ (RealSequences × RationalGroup) :=
  (MeasurableEquiv.addRight h).prodCongr (MeasurableEquiv.refl RationalGroup)

theorem translatedCorner_preserving (h : RealSequences) (hs : Summable (fun n => |h n|)) :
    MeasurePreserving (translatedCornerEquiv h)
      (cornerMeasure (G := RationalGroup) restrictedProductMeasure (translatedCorner h))
      (translationScale h • cornerMeasure (G := RationalGroup) restrictedProductMeasure (stageSet 0)) := by
  let e := MeasurableEquiv.addRight h
  have he : MeasurePreserving e restrictedProductMeasure (translationScale h • restrictedProductMeasure) := by
    refine ⟨e.measurable, ?_⟩
    change restrictedProductMeasure.map (fun x => x + h) =
      (translationScale h : ℝ≥0∞) • restrictedProductMeasure
    rw [map_summable_restrictedProductMeasure h hs,
      ENNReal.ofReal_eq_coe_nnreal (Real.exp_pos _).le]
    rfl
  have heA := he.restrict_preimage_emb e.measurableEmbedding (stageSet 0)
  have hF := heA.prod (MeasurePreserving.id (Measure.count : Measure RationalGroup))
  change MeasurePreserving (translatedCornerEquiv h)
    ((restrictedProductMeasure.restrict (translatedCorner h)).prod Measure.count)
    (((translationScale h : ℝ≥0∞) • restrictedProductMeasure).restrict (stageSet 0) |>.prod Measure.count) at hF
  rw [Measure.restrict_smul, Measure.prod_smul_left] at hF
  exact hF



def translatedCornerPullback (h : RealSequences) (hs : Summable (fun n => |h n|)) :
    Lp ℂ 2 (translationScale h • cornerMeasure (G := RationalGroup) restrictedProductMeasure (stageSet 0)) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (cornerMeasure (G := RationalGroup) restrictedProductMeasure (translatedCorner h)) :=
  pullbackUnitary _ _ (translatedCornerEquiv h) (translatedCornerEquiv h).symm
    (translatedCorner_preserving h hs) ((translatedCorner_preserving h hs).symm (translatedCornerEquiv h))
    (Eventually.of_forall (fun p => (translatedCornerEquiv h).symm_apply_apply p))



end MeasureEquivalenceRestrictedPhase


