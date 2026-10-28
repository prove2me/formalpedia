-- Prove2me | solution 1 for MeasureUnitary.vectorCantorMultiplier_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T13:33:32.0168+00:00
-- url     : https://prove2.me/submissions/88cc23c4-ffe0-4a7a-b4e3-23346f4c4f3d

import Definitions.Def_BenchmarkOperator20261026_HilbertSequenceTopology
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorAmplified
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorDenseFamily
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorGram
import Definitions.Def_BenchmarkOperator20261026_MeasureCantorTuple
import Definitions.Def_BenchmarkOperator20261026_MeasureL2Constants
import Definitions.Def_BenchmarkOperator20261026_MeasureUnitaryMultipliers
import Definitions.Def_BenchmarkOperator20261026_OperatorFreeGroup
import Definitions.Def_BenchmarkOperator20261026_OperatorStrongUnitary
import Definitions.Def_BenchmarkOperator20261026_OperatorTargets
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Data.Nat.Nth
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
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

-- Preserved source skeleton: MeasureCantorGram
section
/-! Measurable Gram matrices for the explicit varying-measure L² family.
The parameter measurable structure is the genuine Giry structure on
probability measures, and all entries are actual L² inner products. -/

open MeasureTheory Set Filter
open scoped ENNReal

namespace MeasureUnitary









theorem cantorIntersectionIndex_spec (k l : CantorCylinderIndex) :
    cantorCylinder (cantorIntersectionIndex k l) = cantorCylinder k ∩ cantorCylinder l :=
  (cantorCylinder_isSetAlgebra.inter_mem ⟨k, rfl⟩ ⟨l, rfl⟩).choose_spec



theorem cantorComplementIndex_spec (k : CantorCylinderIndex) :
    cantorCylinder (cantorComplementIndex k) = (cantorCylinder k)ᶜ :=
  (cantorCylinder_isSetAlgebra.compl_mem ⟨k, rfl⟩).choose_spec





end MeasureUnitary

end

/-! Measurable Gram matrices for the explicit varying-measure L² family.
The parameter measurable structure is the genuine Giry structure on
probability measures, and all entries are actual L² inner products. -/
open MeasureTheory Set Filter
open scoped ENNReal
namespace MeasureUnitary
end MeasureUnitary
open MeasureUnitary

theorem solution (μ : Measure CantorSpace) [IsFiniteMeasure μ]
    (r : CantorCylinderIndex) (k : CantorFundamentalIndex) :
    vectorCantorMultiplier μ r (cantorFundamentalVector μ k) =
      cantorFundamentalVector μ (cantorIntersectionIndex r k.1, k.2) -
        cantorFundamentalVector μ (cantorIntersectionIndex (cantorComplementIndex r) k.1, k.2) := by
  change phaseMap μ (cantorCylinderPhase r) (cantorCylinderPhase_measurable r)
    (cantorCylinderPhase_norm r) (cantorFundamentalVector μ k) = _
  apply Lp.ext
  filter_upwards [phaseMap_coe μ (cantorCylinderPhase r) (cantorCylinderPhase_measurable r)
      (cantorCylinderPhase_norm r) (cantorFundamentalVector μ k),
    indicatorConstLp_coeFn (p := 2) (hs := cantorCylinder_measurable k.1)
      (hμs := measure_ne_top μ _) (c := (lp.single 2 k.2 (1 : ℂ) : OperatorCoding.CanonicalHilbert)),
    indicatorConstLp_coeFn (p := 2) (hs := cantorCylinder_measurable (cantorIntersectionIndex r k.1))
      (hμs := measure_ne_top μ _) (c := (lp.single 2 k.2 (1 : ℂ) : OperatorCoding.CanonicalHilbert)),
    indicatorConstLp_coeFn (p := 2)
      (hs := cantorCylinder_measurable (cantorIntersectionIndex (cantorComplementIndex r) k.1))
      (hμs := measure_ne_top μ _) (c := (lp.single 2 k.2 (1 : ℂ) : OperatorCoding.CanonicalHilbert)),
    Lp.coeFn_sub (cantorFundamentalVector μ (cantorIntersectionIndex r k.1, k.2))
      (cantorFundamentalVector μ (cantorIntersectionIndex (cantorComplementIndex r) k.1, k.2))]
    with x hphase hk hpos hneg hsub
  simp only [Pi.sub_apply] at hsub
  simp only [cantorFundamentalVector] at hphase hsub ⊢
  rw [hphase, hsub, hpos, hneg, hk]
  rw [cantorIntersectionIndex_spec, cantorIntersectionIndex_spec, cantorComplementIndex_spec]
  classical
  by_cases hr : x ∈ cantorCylinder r <;> by_cases hk : x ∈ cantorCylinder k.1 <;>
    simp [cantorCylinderPhase, hr, hk]
