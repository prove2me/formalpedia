-- Prove2me | Definitions.Def_BenchmarkOperator20261026_MeasureInducedOperatorCode
-- name    : BenchmarkOperator20261026_MeasureInducedOperatorCode
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:46:04.714987+00:00
-- url     : https://prove2.me/theorems/45c55d7d-af8f-49c6-83dc-1a700981c5e0
-- title:
--   Measure Induced Operator Code
-- statement:
--   Defines group-coordinate test vectors, a Hilbert basis and coordinate equivalence for the induced space, the canonical induced tuple and its bounded-operator code. The retained measurability, orthonormality, density and dimension facts justify these fixed-space constructions.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization MeasureInducedOperatorCode.lean, lines 18–110; source SHA-256 ca61cd3e904c53be699cb7b98cd3bfbcedd6aaaac3ca85a2007c486e13c6f5bd. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_HilbertSequenceTopology
import Definitions.Def_BenchmarkOperator20261026_InducedCornerTransport
import Definitions.Def_BenchmarkOperator20261026_MeasureGramSchmidtBorel
import Definitions.Def_BenchmarkOperator20261026_OperatorBireduction
import Definitions.Def_BenchmarkOperator20261026_OperatorFreeGroup
import Definitions.Def_BenchmarkOperator20261026_OperatorStrongUnitary
import Definitions.Def_BenchmarkOperator20261026_OperatorTargets
import Definitions.Def_BenchmarkOperator20261026_OperatorUnitaryBorel
import Definitions.Def_BenchmarkOperator20261026_RestrictedAction
import Definitions.Def_BenchmarkOperator20261026_RestrictedCompactMeasure
import Definitions.Def_BenchmarkOperator20261026_RestrictedCompatibility
import Definitions.Def_BenchmarkOperator20261026_RestrictedDensity
import Definitions.Def_BenchmarkOperator20261026_RestrictedFiniteModulus
import Definitions.Def_BenchmarkOperator20261026_RestrictedInducedFamily
import Definitions.Def_BenchmarkOperator20261026_RestrictedInducedTuple
import Definitions.Def_BenchmarkOperator20261026_RestrictedPhaseFamily
import Definitions.Def_BenchmarkOperator20261026_RestrictedProduct
import Definitions.Def_BenchmarkOperator20261026_RestrictedStages
import Definitions.Def_BenchmarkOperator20261026_SolenoidGroups
import Definitions.Def_BenchmarkOperator20261026_SumFiberCoordinates
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Set.Lattice
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Nat
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.ProjectiveFamilyContent
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
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
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
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

/-! Canonical fixed-space realization and bounded-operator coding of the
actual restricted-product induced representation family. -/

open MeasureTheory Set Filter Topology TopologicalSpace OperatorCoding InnerProductSpace
open scoped ENNReal

namespace MeasureEquivalenceRestrictedPhase

open MeasureEquivalenceRestrictedProduct MeasureEquivalenceSolenoid MeasureEquivalenceInducedCorners

noncomputable section

instance inducedHilbert_secondCountable : SecondCountableTopology InducedHilbert := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  letI : SigmaFinite (cornerMeasure (G := RationalGroup) restrictedProductMeasure (stageSet 0)) := by
    rw [base_corner_measure_eq_base_product]
    infer_instance
  infer_instance

def rationalNatElement (n : ℕ) : RationalGroup := Multiplicative.ofAdd
  (⟨Finsupp.single 0 (n : ℚ) - Finsupp.single 1 (n : ℚ), by
    change rationalTotal (Finsupp.single 0 (n : ℚ) - Finsupp.single 1 (n : ℚ)) = 0
    rw [map_sub]
    simp [rationalTotal, Finsupp.liftAddHom_apply]⟩ : rationalZeroSumGroup)

theorem rationalNatElement_injective : Function.Injective rationalNatElement := by
  intro m n h
  have hh := congrArg (fun q : RationalGroup =>
    ((Multiplicative.toAdd q : rationalZeroSumGroup) : ℕ →₀ ℚ) 0) h
  change (Finsupp.single 0 (m : ℚ) - Finsupp.single 1 (m : ℚ) : ℕ →₀ ℚ) 0 =
    (Finsupp.single 0 (n : ℚ) - Finsupp.single 1 (n : ℚ) : ℕ →₀ ℚ) 0 at hh
  simp only [Finsupp.sub_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (by decide : (0 : ℕ) ≠ 1), sub_zero] at hh
  exact_mod_cast hh

def inducedGroupCell (g : RationalGroup) : Set (RealSequences × RationalGroup) := Set.univ ×ˢ {g}

theorem inducedGroupCell_measurable (g : RationalGroup) : MeasurableSet (inducedGroupCell g) :=
  MeasurableSet.univ.prod (measurableSet_singleton g)

theorem inducedGroupCell_measure (g : RationalGroup) :
    cornerMeasure (G := RationalGroup) restrictedProductMeasure (stageSet 0) (inducedGroupCell g) = 1 := by
  rw [base_corner_measure_eq_base_product]
  simp [inducedGroupCell, Measure.prod_prod]

def inducedGroupVector (g : RationalGroup) : InducedHilbert :=
  indicatorConstLp 2 (inducedGroupCell_measurable g)
    (by rw [inducedGroupCell_measure]; exact ENNReal.one_ne_top) (1 : ℂ)

theorem inducedGroupVector_orthonormal : Orthonormal ℂ inducedGroupVector := by
  classical
  rw [orthonormal_iff_ite]
  intro g h
  rw [inducedGroupVector, inducedGroupVector,
    L2.inner_indicatorConstLp_one_indicatorConstLp_one (inducedGroupCell_measurable g)
      (inducedGroupCell_measurable h) (by rw [inducedGroupCell_measure]; exact ENNReal.one_ne_top)
      (by rw [inducedGroupCell_measure]; exact ENNReal.one_ne_top)]
  by_cases he : g = h
  · subst h
    simp only [Set.inter_self, if_true, measureReal_def, inducedGroupCell_measure, ENNReal.toReal_one]
    norm_num
  · have hdis : inducedGroupCell g ∩ inducedGroupCell h = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact he (hp.1.2.symm.trans hp.2.2)
    simp [hdis, he]

theorem inducedHilbert_not_finiteDimensional : ¬ FiniteDimensional ℂ InducedHilbert := by
  intro h
  letI := h
  have hi := (inducedGroupVector_orthonormal.comp rationalNatElement rationalNatElement_injective).linearIndependent
  exact Module.Finite.not_linearIndependent_of_infinite _ hi

local instance _root_.MeasureEquivalenceRestrictedPhase.instMeasurableSpaceSubtypeAEEqFunProdRealSequencesRationalGroupComplexCornerMeasureRestrictedProductMeasureStageSetOfNatNatMemAddSubgroupInducedHilbert_measureInducedOperatorCode : MeasurableSpace InducedHilbert := borel _
local instance _root_.MeasureEquivalenceRestrictedPhase.instBorelSpaceSubtypeAEEqFunProdRealSequencesRationalGroupComplexCornerMeasureRestrictedProductMeasureStageSetOfNatNatMemAddSubgroupInducedHilbert_measureInducedOperatorCode : BorelSpace InducedHilbert := ⟨rfl⟩

theorem inducedDenseSequence_dense_span :
    (Submodule.span ℂ (Set.range (denseSeq InducedHilbert))).topologicalClosure = ⊤ := by
  apply top_unique
  intro x hx
  have hd : Dense (Set.range (denseSeq InducedHilbert)) := denseRange_denseSeq InducedHilbert
  exact closure_mono (Submodule.subset_span) (hd x)

def inducedCanonicalHilbertBasis : HilbertBasis ℕ ℂ InducedHilbert :=
  MeasureUnitary.selectedGramSchmidtBasis (fun _ : Unit => denseSeq InducedHilbert)
    (fun _ => MeasureUnitary.gramSchmidtNormed_nonzero_infinite (denseSeq InducedHilbert)
      inducedDenseSequence_dense_span inducedHilbert_not_finiteDimensional)
    (fun _ => inducedDenseSequence_dense_span) ()

def inducedCanonicalCoordinates : InducedHilbert ≃ₗᵢ[ℂ] CanonicalHilbert := inducedCanonicalHilbertBasis.repr

def canonicalInducedTuple (k : CompactSequences) (n : ℕ) : StrongUnitary CanonicalHilbert :=
  inducedCanonicalCoordinates.symm.trans ((inducedTuple k n).trans inducedCanonicalCoordinates)



def inducedCodedOperator (k : CompactSequences) : CanonicalOperator :=
  canonicalTupleCodedOperator (canonicalInducedTuple k)





end

end MeasureEquivalenceRestrictedPhase


