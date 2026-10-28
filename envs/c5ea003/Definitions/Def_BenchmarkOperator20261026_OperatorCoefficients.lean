-- Prove2me | Definitions.Def_BenchmarkOperator20261026_OperatorCoefficients
-- name    : BenchmarkOperator20261026_OperatorCoefficients
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:45:11.840819+00:00
-- url     : https://prove2.me/theorems/2a04921d-a852-45af-8476-f0d1bbdc7513
-- title:
--   Operator Coefficients
-- statement:
--   Defines extraction of a bounded operator entry between specified Hilbert-sum coordinates. The retained formulas evaluate the diagonal marker on coordinate vectors. Later theorem nodes use these entries to recover the encoded unitary tuple.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization OperatorCoefficients.lean, lines 13–55; source SHA-256 c00cd3b70a50e860d857b4a24f3acc6ec3c7ce5d719ce00f4b3435d3681afa20. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_OperatorBlocks
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

/-! Matrix entries of the actual norm-convergent operator coding. -/

open ContinuousLinearMap

namespace OperatorCoding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def operatorCoordinate (x : HilbertSum H) (i : ℕ) :
    (HilbertSum H →L[ℂ] HilbertSum H) →L[ℂ] H :=
  (lp.evalCLM ℂ (fun _ : ℕ => H) 2 i).comp
    (ContinuousLinearMap.apply ℂ (HilbertSum H) x)

theorem operatorCoordinate_apply (x : HilbertSum H) (i : ℕ)
    (T : HilbertSum H →L[ℂ] HilbertSum H) :
    operatorCoordinate x i T = T x i := rfl







theorem tupleDiagonal_coordinate (x : HilbertSum H) (i : ℕ) :
    tupleDiagonal x i = (((1 / 2 : ℝ) * (1 / 2 : ℝ) ^ i : ℝ) : ℂ) • x i := by
  change operatorCoordinate x i tupleDiagonal = _
  rw [tupleDiagonal, (operatorCoordinate x i).map_tsum summable_tupleDiagonal]
  rw [tsum_eq_single i]
  · simp [operatorCoordinate_apply, weightedOperator, identityBlock,
      ContinuousLinearMap.smul_apply, lp.coeFn_smul, blockOperator_coordinate]
  · intro j hji
    simp [operatorCoordinate_apply, weightedOperator, identityBlock,
      ContinuousLinearMap.smul_apply, lp.coeFn_smul, blockOperator_coordinate,
      Ne.symm hji]

theorem tupleDiagonal_single (i : ℕ) (x : H) :
    tupleDiagonal (lp.single 2 i x) =
      lp.single 2 i (((((1 / 2 : ℝ) * (1 / 2 : ℝ) ^ i : ℝ) : ℂ)) • x) := by
  apply lp.ext
  funext j
  rw [tupleDiagonal_coordinate]
  by_cases h : j = i
  · subst j
    simp [lp.single_apply]
  · simp [lp.single_apply, h]





end OperatorCoding


