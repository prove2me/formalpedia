-- Prove2me | Definitions.Def_BenchmarkOperator20261026_OperatorBlocks
-- name    : BenchmarkOperator20261026_OperatorBlocks
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:37:15.29098+00:00
-- url     : https://prove2.me/theorems/eac614e1-7dd0-49e6-93ab-206580a83780
-- title:
--   Operator Blocks
-- statement:
--   Defines a countable Hilbert sum and a bounded operator inserting a given bounded map between two specified blocks. The retained coordinate formulas and norm bound justify these block operators for use in the coding series.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization OperatorBlocks.lean, lines 18–39; source SHA-256 22f22190fd48f4a192c3b87b7637d78a4b3c10c12d9599c7feb78b71317943b9. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_OperatorFreeGroup
import Definitions.Def_BenchmarkOperator20261026_OperatorStrongUnitary
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
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

/-!
Concrete block operators on a countable Hilbert sum, for the tuple coding.
All blocks are actual bounded operators; the estimates below justify the
operator-norm convergence of the weighted series in the manuscript.
-/

open ContinuousLinearMap
open scoped ENNReal

namespace OperatorCoding

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

abbrev HilbertSum (H : Type*) [NormedAddCommGroup H] := lp (fun _ : ℕ => H) 2

noncomputable def blockOperator (i j : ℕ) (A : H →L[ℂ] H) :
    HilbertSum H →L[ℂ] HilbertSum H :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => H) 2 i).comp
    (A.comp (lp.evalCLM ℂ (fun _ : ℕ => H) 2 j))

theorem blockOperator_apply (i j : ℕ) (A : H →L[ℂ] H) (x : HilbertSum H) :
    blockOperator i j A x = lp.single 2 i (A (x j)) := rfl

theorem blockOperator_coordinate (i j k : ℕ) (A : H →L[ℂ] H) (x : HilbertSum H) :
    blockOperator i j A x k = if k = i then A (x j) else 0 := by
  simp [blockOperator_apply, lp.single_apply, Pi.single_apply]

theorem blockOperator_norm_le (i j : ℕ) (A : H →L[ℂ] H) :
    ‖blockOperator i j A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro x
  rw [blockOperator_apply, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  exact (A.le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) x j)
      (norm_nonneg A))









variable [CompleteSpace H]



end OperatorCoding


