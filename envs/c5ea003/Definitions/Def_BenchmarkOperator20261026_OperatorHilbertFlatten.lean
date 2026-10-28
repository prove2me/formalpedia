-- Prove2me | Definitions.Def_BenchmarkOperator20261026_OperatorHilbertFlatten
-- name    : BenchmarkOperator20261026_OperatorHilbertFlatten
-- status  : Definition
-- author  : @username
-- created : 2026-10-26T10:38:04.592239+00:00
-- url     : https://prove2.me/theorems/dd207114-f8f9-4774-a0e3-559ef13905ea
-- title:
--   Operator Hilbert Flatten
-- statement:
--   Defines Hilbert-space equivalences between a countable sum of canonical $\ell_2$ spaces, a matrix-indexed $\ell_2$ space, and one canonical $\ell_2$ space. The retained norm identity justifies flattening. These maps put the tuple coding on a fixed Hilbert space.
-- source:
--   Ruijun Wang, Comparisons of benchmark equivalence relations, Theorem 1.5 (formerly MeasureEquivalence.tex, Theorem 1.3); local formalization OperatorHilbertFlatten.lean, lines 14–109; source SHA-256 3e893b536ef1b553e02a4d0a26a36008a302dd5f3388a782f8a2349866df3538. Designated upload repository: https://github.com/RayjunWang/Benchmark (no source commit published yet).

import Definitions.Def_BenchmarkOperator20261026_HilbertSequenceTopology
import Definitions.Def_BenchmarkOperator20261026_OperatorBlocks
import Definitions.Def_BenchmarkOperator20261026_OperatorFreeGroup
import Definitions.Def_BenchmarkOperator20261026_OperatorStrongUnitary
import Definitions.Def_BenchmarkOperator20261026_OperatorTargets
import Definitions.Def_BenchmarkOperator20261026_OperatorUnitaryBorel
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Logic.Equiv.Nat
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.Real
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

/-! A fixed, explicit Hilbert-space identification for the tuple coding:
ℓ²(ℕ, ℓ²(ℕ, ℂ)) ≃ ℓ²(ℕ × ℕ, ℂ) ≃ ℓ²(ℕ, ℂ). -/

open scoped ENNReal

namespace OperatorCoding

noncomputable section

abbrev MatrixHilbert := lp (fun _ : ℕ × ℕ => ℂ) 2

def flattenHilbertSum (x : HilbertSum CanonicalHilbert) : MatrixHilbert :=
  ⟨fun p => x p.1 p.2, by
    apply memℓp_gen
    apply (summable_prod_of_nonneg (fun p : ℕ × ℕ => by positivity)).mpr
    constructor
    · intro i
      exact (x i).property.summable (by norm_num)
    · have hrow : ∀ i, (∑' j, ‖x i j‖ ^ (2 : ℝ≥0∞).toReal) = ‖x i‖ ^ (2 : ℝ≥0∞).toReal :=
        fun i => (lp.norm_rpow_eq_tsum (by norm_num) (x i)).symm
      simp_rw [hrow]
      exact x.property.summable (by norm_num)⟩

def matrixHilbertRow (y : MatrixHilbert) (i : ℕ) : CanonicalHilbert :=
  ⟨fun j => y (i, j), by
    apply memℓp_gen
    exact ((summable_prod_of_nonneg (fun p : ℕ × ℕ => by positivity)).mp
      (y.property.summable (by norm_num))).1 i⟩

def foldMatrixHilbert (y : MatrixHilbert) : HilbertSum CanonicalHilbert :=
  ⟨fun i => matrixHilbertRow y i, by
    apply memℓp_gen
    have hrows := ((summable_prod_of_nonneg (fun p : ℕ × ℕ => by positivity)).mp
      (y.property.summable (by norm_num))).2
    have heq : (fun i => ‖matrixHilbertRow y i‖ ^ (2 : ℝ≥0∞).toReal) =
        (fun i => ∑' j, ‖y (i, j)‖ ^ (2 : ℝ≥0∞).toReal) := by
      funext i
      exact lp.norm_rpow_eq_tsum (by norm_num) (matrixHilbertRow y i)
    rw [heq]
    exact hrows⟩

theorem flattenHilbertSum_norm (x : HilbertSum CanonicalHilbert) : ‖flattenHilbertSum x‖ = ‖x‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
  congr 1
  change (∑' p : ℕ × ℕ, ‖x p.1 p.2‖ ^ (2 : ℝ≥0∞).toReal) =
    ∑' i, ‖x i‖ ^ (2 : ℝ≥0∞).toReal
  have hfubini := ((flattenHilbertSum x).property.summable (by norm_num)).tsum_prod'
    (fun i => (x i).property.summable (by norm_num))
  change (∑' p : ℕ × ℕ, ‖x p.1 p.2‖ ^ (2 : ℝ≥0∞).toReal) =
    ∑' i, ∑' j, ‖x i j‖ ^ (2 : ℝ≥0∞).toReal at hfubini
  rw [hfubini]
  apply tsum_congr
  intro i
  exact (lp.norm_rpow_eq_tsum (by norm_num) (x i)).symm

def hilbertSumMatrixEquiv : HilbertSum CanonicalHilbert ≃ₗᵢ[ℂ] MatrixHilbert where
  toLinearEquiv :=
    { toFun := flattenHilbertSum
      invFun := foldMatrixHilbert
      left_inv := by
        intro x
        apply lp.ext
        funext i
        apply lp.ext
        funext j
        rfl
      right_inv := by
        intro y
        apply lp.ext
        funext p
        rfl
      map_add' := by
        intro x y
        apply lp.ext
        funext p
        rfl
      map_smul' := by
        intro c x
        apply lp.ext
        funext p
        rfl }
  norm_map' := flattenHilbertSum_norm

def reindexHilbert {I J : Type*} (e : I ≃ J) :
    lp (fun _ : I => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : J => ℂ) 2 where
  toLinearEquiv :=
    { toFun := fun x => ⟨fun j => x (e.symm j), by
        apply memℓp_gen
        exact e.symm.summable_iff.mpr (x.property.summable (by norm_num))⟩
      invFun := fun y => ⟨fun i => y (e i), by
        apply memℓp_gen
        exact e.summable_iff.mpr (y.property.summable (by norm_num))⟩
      left_inv := by intro x; apply lp.ext; funext i; exact congrArg x (e.symm_apply_apply i)
      right_inv := by intro y; apply lp.ext; funext j; exact congrArg y (e.apply_symm_apply j)
      map_add' := by intro x y; apply lp.ext; funext j; rfl
      map_smul' := by intro c x; apply lp.ext; funext j; rfl }
  norm_map' := by
    intro x
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact e.symm.tsum_eq (fun i => ‖x i‖ ^ (2 : ℝ≥0∞).toReal)

/-- The fixed canonical identification used after the countable tuple coding. -/
def canonicalHilbertSumEquiv : HilbertSum CanonicalHilbert ≃ₗᵢ[ℂ] CanonicalHilbert :=
  hilbertSumMatrixEquiv.trans (reindexHilbert Nat.pairEquiv)

end
end OperatorCoding


