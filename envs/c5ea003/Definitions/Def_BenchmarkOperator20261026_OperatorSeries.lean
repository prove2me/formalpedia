-- Prove2me | Definitions.Def_BenchmarkOperator20261026_OperatorSeries
-- name    : BenchmarkOperator20261026_OperatorSeries
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:38:29.848082+00:00
-- url     : https://prove2.me/theorems/f1e53756-5f27-457f-89c6-9cc7a3297eef
-- title:
--   Operator Series
-- statement:
--   Defines the identity, star and tuple connectors, their geometric weighting, the diagonal marker, and the bounded operator coding a unitary tuple. The summability and norm bounds needed to form the defining operator series are retained. Conjugacy recovery is proved later.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization OperatorSeries.lean, lines 15–106; source SHA-256 a23472d990cfaf0cd622a00370f9e989909cfbd045d8b105e99fa954e4d96139. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_OperatorBlocks
import Definitions.Def_BenchmarkOperator20261026_OperatorFreeGroup
import Definitions.Def_BenchmarkOperator20261026_OperatorStrongUnitary
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

/-! The norm-convergent series of the countable unitary-tuple coding. -/

open ContinuousLinearMap

namespace OperatorCoding

set_option maxHeartbeats 1000000

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def weightedOperator (c : ℝ) (n : ℕ)
    (A : HilbertSum H →L[ℂ] HilbertSum H) : HilbertSum H →L[ℂ] HilbertSum H :=
  (((c * (1 / 2 : ℝ) ^ n : ℝ)) : ℂ) • A

theorem weightedOperator_norm_le {A : ℕ → HilbertSum H →L[ℂ] HilbertSum H}
    {C : ℝ} (hC : ∀ n, ‖A n‖ ≤ C) (c : ℝ) (n : ℕ) :
    ‖weightedOperator c n (A n)‖ ≤ (|c| * C) * (1 / 2 : ℝ) ^ n := by
  calc
    ‖weightedOperator c n (A n)‖ ≤ ‖((c * (1 / 2 : ℝ) ^ n : ℝ) : ℂ)‖ * ‖A n‖ :=
      ContinuousLinearMap.opNorm_smul_le (((c * (1 / 2 : ℝ) ^ n : ℝ)) : ℂ) (A n)
    _ = |c| * (1 / 2 : ℝ) ^ n * ‖A n‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    _ ≤ |c| * (1 / 2 : ℝ) ^ n * C := by
      apply mul_le_mul_of_nonneg_left (hC n)
      positivity
    _ = (|c| * C) * (1 / 2 : ℝ) ^ n := by ring

theorem summable_weightedOperator {A : ℕ → HilbertSum H →L[ℂ] HilbertSum H}
    {C : ℝ} (hC : ∀ n, ‖A n‖ ≤ C) (c : ℝ) :
    Summable (fun n => weightedOperator c n (A n)) := by
  exact ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (|c| * C)).of_norm_bounded
      (f := fun n => weightedOperator c n (A n)) (weightedOperator_norm_le hC c)



noncomputable def identityBlock (i j : ℕ) : HilbertSum H →L[ℂ] HilbertSum H :=
  blockOperator i j (ContinuousLinearMap.id ℂ H)

theorem identityBlock_norm_le (i j : ℕ) : ‖identityBlock (H := H) i j‖ ≤ 1 :=
  (blockOperator_norm_le _ _ _).trans ContinuousLinearMap.norm_id_le

noncomputable def starConnector (n : ℕ) : HilbertSum H →L[ℂ] HilbertSum H :=
  identityBlock 0 (n + 1) + identityBlock (n + 1) 0





noncomputable def tupleConnector (u : ℕ → StrongUnitary H) (n : ℕ) :
    HilbertSum H →L[ℂ] HilbertSum H :=
  blockOperator (2 * n + 1) (2 * n + 2) (u n : H →L[ℂ] H) +
  blockOperator (2 * n + 2) (2 * n + 1) (u n : H →L[ℂ] H).adjoint



noncomputable def tupleDiagonal : HilbertSum H →L[ℂ] HilbertSum H :=
  ∑' n, weightedOperator (1 / 2) n (identityBlock n n)

noncomputable def tupleImaginaryPart (u : ℕ → StrongUnitary H) :
    HilbertSum H →L[ℂ] HilbertSum H :=
  (∑' n, weightedOperator (1 / 32) n (starConnector n)) +
  (∑' n, weightedOperator (1 / 16) n (tupleConnector u n))

noncomputable def tupleCodedOperator (u : ℕ → StrongUnitary H) :
    HilbertSum H →L[ℂ] HilbertSum H :=
  tupleDiagonal + Complex.I • tupleImaginaryPart u

theorem summable_tupleDiagonal :
    Summable (fun n => weightedOperator (H := H) (1 / 2) n (identityBlock n n)) :=
  summable_weightedOperator (fun n => identityBlock_norm_le n n) _







end OperatorCoding


