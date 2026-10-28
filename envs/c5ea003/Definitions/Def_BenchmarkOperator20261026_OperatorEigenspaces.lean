-- Prove2me | Definitions.Def_BenchmarkOperator20261026_OperatorEigenspaces
-- name    : BenchmarkOperator20261026_OperatorEigenspaces
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:46:16.306044+00:00
-- url     : https://prove2.me/theorems/7cc3b402-2623-42e4-8204-23674a1b5a9b
-- title:
--   Operator Eigenspaces
-- statement:
--   Defines the distinct diagonal marker eigenvalues, restrictions of a commuting unitary to its marker blocks, and the resulting block unitaries. The retained support and isometry identities justify these restrictions. They are the data used by conjugacy recovery.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization OperatorEigenspaces.lean, lines 11–99; source SHA-256 c6e256a974455d69bd2c26d2b5a66a5a3ec8dce4e8a30b6b28a757ad58e235ec. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_OperatorBlocks
import Definitions.Def_BenchmarkOperator20261026_OperatorCoefficients
import Definitions.Def_BenchmarkOperator20261026_OperatorFreeGroup
import Definitions.Def_BenchmarkOperator20261026_OperatorSeries
import Definitions.Def_BenchmarkOperator20261026_OperatorStrongUnitary
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
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
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
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

/-! The diagonal marker separates all countably many Hilbert summands. -/

namespace OperatorCoding

open scoped ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def diagonalEigenvalue (i : ℕ) : ℂ :=
  (((1 / 2 : ℝ) * (1 / 2 : ℝ) ^ i : ℝ) : ℂ)

theorem diagonalEigenvalue_injective : Function.Injective diagonalEigenvalue := by
  intro i j h
  have hr : (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ i = (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ j :=
    Complex.ofReal_injective h
  have hp : (1 / 2 : ℝ) ^ i = (1 / 2 : ℝ) ^ j :=
    mul_left_cancel₀ (by norm_num : (1 / 2 : ℝ) ≠ 0) hr
  exact pow_right_injective₀ (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≠ 1) hp

theorem tupleDiagonal_eigenvector_support (x : HilbertSum H) (j i : ℕ)
    (hx : tupleDiagonal x = diagonalEigenvalue j • x) (hij : i ≠ j) : x i = 0 := by
  have hcoord := congrArg (fun z : HilbertSum H => z i) hx
  dsimp only at hcoord
  rw [tupleDiagonal_coordinate] at hcoord
  change diagonalEigenvalue i • x i = diagonalEigenvalue j • x i at hcoord
  have hz : (diagonalEigenvalue i - diagonalEigenvalue j) • x i = 0 := by
    rw [sub_smul, hcoord, sub_self]
  have hne : diagonalEigenvalue i - diagonalEigenvalue j ≠ 0 :=
    sub_ne_zero.mpr (fun h => hij (diagonalEigenvalue_injective h))
  exact (smul_eq_zero.mp hz).resolve_left hne

theorem tupleDiagonal_eigenvector_single (x : HilbertSum H) (j : ℕ)
    (hx : tupleDiagonal x = diagonalEigenvalue j • x) : x = lp.single 2 j (x j) := by
  apply lp.ext
  funext i
  by_cases h : i = j
  · subst i
    simp [lp.single_apply]
  · rw [tupleDiagonal_eigenvector_support x j i hx h]
    simp [lp.single_apply, h]

theorem tupleDiagonal_single_eigenvector (j : ℕ) (x : H) :
    tupleDiagonal (lp.single 2 j x) = diagonalEigenvalue j • lp.single 2 j x := by
  rw [tupleDiagonal_single]
  exact lp.single_smul 2 j _ _

noncomputable def diagonalRestriction (Q : StrongUnitary (HilbertSum H)) (j : ℕ) : H →L[ℂ] H :=
  (lp.evalCLM ℂ (fun _ : ℕ => H) 2 j).comp
    ((Q : HilbertSum H →L[ℂ] HilbertSum H).comp
      (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => H) 2 j))



theorem commutingDiagonal_single (Q : StrongUnitary (HilbertSum H))
    (hQ : ∀ x, Q (tupleDiagonal x) = tupleDiagonal (Q x)) (j : ℕ) (x : H) :
    Q (lp.single 2 j x) = lp.single 2 j (diagonalRestriction Q j x) := by
  apply tupleDiagonal_eigenvector_single
  rw [← hQ, tupleDiagonal_single_eigenvector, Q.map_smul]

theorem diagonalRestriction_norm (Q : StrongUnitary (HilbertSum H))
    (hQ : ∀ x, Q (tupleDiagonal x) = tupleDiagonal (Q x)) (j : ℕ) (x : H) :
    ‖diagonalRestriction Q j x‖ = ‖x‖ := by
  have h₁ := lp.norm_single (E := fun _ : ℕ => H) (p := 2)
    (by norm_num) j (diagonalRestriction Q j x)
  have h₂ := lp.norm_single (E := fun _ : ℕ => H) (p := 2) (by norm_num) j x
  calc
    ‖diagonalRestriction Q j x‖ = ‖(lp.single 2 j (diagonalRestriction Q j x) : HilbertSum H)‖ :=
      h₁.symm
    _ = ‖Q (lp.single 2 j x)‖ := congrArg norm (commutingDiagonal_single Q hQ j x).symm
    _ = ‖(lp.single 2 j x : HilbertSum H)‖ := Q.norm_map' (lp.single 2 j x)
    _ = ‖x‖ := h₂

theorem commutingDiagonal_inverse (Q : StrongUnitary (HilbertSum H))
    (hQ : ∀ x, Q (tupleDiagonal x) = tupleDiagonal (Q x)) :
    ∀ x, Q.symm (tupleDiagonal x) = tupleDiagonal (Q.symm x) := by
  intro x
  apply Q.injective
  simpa using (hQ (Q.symm x)).symm

theorem diagonalRestriction_surjective (Q : StrongUnitary (HilbertSum H))
    (hQ : ∀ x, Q (tupleDiagonal x) = tupleDiagonal (Q x)) (j : ℕ) :
    Function.Surjective (diagonalRestriction Q j) := by
  intro x
  refine ⟨diagonalRestriction Q.symm j x, ?_⟩
  apply (lp.isometry_single (E := fun _ : ℕ => H) (p := 2) j).injective
  rw [← commutingDiagonal_single Q hQ j]
  rw [← commutingDiagonal_single Q.symm (commutingDiagonal_inverse Q hQ) j]
  exact Q.apply_symm_apply _

noncomputable def diagonalBlockUnitary (Q : StrongUnitary (HilbertSum H))
    (hQ : ∀ x, Q (tupleDiagonal x) = tupleDiagonal (Q x)) (j : ℕ) : StrongUnitary H :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (diagonalRestriction Q j).toLinearMap
      norm_map' := diagonalRestriction_norm Q hQ j }
    (diagonalRestriction_surjective Q hQ j)





end OperatorCoding


