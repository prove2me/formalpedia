-- Prove2me | solution 1 for OperatorCoding.tupleImaginaryPart_tuple_entry
-- status  : ACCEPTED   (prove)
-- author  : @username
-- created : 2026-10-26T13:37:27.255401+00:00
-- url     : https://prove2.me/submissions/457e97a8-3a95-4b75-8b57-8baa50d3c6c4

import Definitions.Def_BenchmarkOperator20261026_OperatorBlocks
import Definitions.Def_BenchmarkOperator20261026_OperatorCoefficients
import Definitions.Def_BenchmarkOperator20261026_OperatorFreeGroup
import Definitions.Def_BenchmarkOperator20261026_OperatorSeries
import Definitions.Def_BenchmarkOperator20261026_OperatorStrongUnitary
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
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

-- Preserved source skeleton: OperatorSeries
section
/-! The norm-convergent series of the countable unitary-tuple coding. -/

open ContinuousLinearMap

namespace OperatorCoding

set_option maxHeartbeats 1000000

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]















theorem starConnector_norm_le (n : ℕ) : ‖starConnector (H := H) n‖ ≤ 2 := by
  unfold starConnector
  exact (norm_add_le (identityBlock (H := H) 0 (n + 1)) (identityBlock (H := H) (n + 1) 0)).trans (by
    have h₁ := identityBlock_norm_le (H := H) 0 (n + 1)
    have h₂ := identityBlock_norm_le (H := H) (n + 1) 0
    linarith)

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









theorem summable_starConnectors :
    Summable (fun n => weightedOperator (H := H) (1 / 32) n (starConnector n)) :=
  summable_weightedOperator starConnector_norm_le _

theorem summable_tupleConnectors (u : ℕ → StrongUnitary H) :
    Summable (fun n => weightedOperator (1 / 16) n (tupleConnector u n)) :=
  summable_weightedOperator (tupleConnector_norm_le u) _



end OperatorCoding

end

-- Preserved source skeleton: OperatorCoefficients
section
/-! Matrix entries of the actual norm-convergent operator coding. -/

open ContinuousLinearMap

namespace OperatorCoding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]





theorem weightedOperator_coordinate (c : ℝ) (n : ℕ)
    (A : HilbertSum H →L[ℂ] HilbertSum H) (x : HilbertSum H) (i : ℕ) :
    weightedOperator c n A x i = (((c * (1 / 2 : ℝ) ^ n : ℝ)) : ℂ) • (A x i) := rfl

theorem starConnector_coordinate (n : ℕ) (x : HilbertSum H) (i : ℕ) :
    starConnector n x i = identityBlock 0 (n + 1) x i + identityBlock (n + 1) 0 x i := rfl

theorem tupleConnector_coordinate (u : ℕ → StrongUnitary H) (n : ℕ) (x : HilbertSum H) (i : ℕ) :
    tupleConnector u n x i =
      blockOperator (2 * n + 1) (2 * n + 2) (u n : H →L[ℂ] H) x i +
      blockOperator (2 * n + 2) (2 * n + 1) (u n : H →L[ℂ] H).adjoint x i := rfl









end OperatorCoding

end

/-! Matrix entries of the actual norm-convergent operator coding. -/
open ContinuousLinearMap
namespace OperatorCoding
end OperatorCoding
open OperatorCoding
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem solution (u : ℕ → StrongUnitary H) (n : ℕ) (x : H) :
    tupleImaginaryPart u (lp.single 2 (2 * n + 2) x) (2 * n + 1) =
      ((((1 / 16 : ℝ) * (1 / 2 : ℝ) ^ n : ℝ) : ℂ)) • u n x := by
  change operatorCoordinate (lp.single 2 (2 * n + 2) x) (2 * n + 1) (tupleImaginaryPart u) = _
  rw [tupleImaginaryPart, map_add,
    (operatorCoordinate _ _).map_tsum summable_starConnectors,
    (operatorCoordinate _ _).map_tsum (summable_tupleConnectors u)]
  have hzero : (∑' k, operatorCoordinate (lp.single 2 (2 * n + 2) x) (2 * n + 1)
      (weightedOperator (1 / 32) k (starConnector k))) = 0 := by
    apply Eq.trans (b := ∑' _ : ℕ, (0 : H))
    · apply tsum_congr
      intro k
      have h₁ : 2 * n + 1 ≠ 0 := by omega
      have h₂ : (0 : ℕ) ≠ 2 * n + 2 := by omega
      simp [operatorCoordinate_apply, weightedOperator_coordinate, starConnector_coordinate, identityBlock,
        blockOperator_coordinate, lp.single_apply, lp.coeFn_add, Pi.add_apply, Pi.smul_apply, h₁, h₂]
    · simp
  rw [hzero, zero_add, tsum_eq_single n]
  · have h : 2 * n + 1 ≠ 2 * n + 2 := by omega
    simp [operatorCoordinate_apply, weightedOperator_coordinate, tupleConnector_coordinate,
      blockOperator_coordinate, lp.single_apply, lp.coeFn_add, Pi.add_apply, Pi.smul_apply, h]
  · intro k hkn
    have h₁ : 2 * n + 1 ≠ 2 * k + 1 := by omega
    have h₂ : 2 * n + 1 ≠ 2 * k + 2 := by omega
    have h₃ : n ≠ k := Ne.symm hkn
    have h₄ : 2 * n ≠ 2 * k + 1 := by omega
    simp [operatorCoordinate_apply, weightedOperator_coordinate, tupleConnector_coordinate,
      blockOperator_coordinate, lp.single_apply, h₁, h₂, h₃, h₄]
