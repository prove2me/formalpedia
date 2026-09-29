-- Prove2me | Definitions.Def_ErdosProblems_Erdos249_PaperCompleteR8_KernelRelationBasis_v2
-- name    : ErdosProblems_Erdos249_PaperCompleteR8_KernelRelationBasis_v2
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-28T16:55:39.947062+00:00
-- url     : https://prove2.me/theorems/80df59f6-d694-4631-98e7-2711e526dc1f
-- title:
--   Integral totient relation coordinates
-- statement:
--   Defines the integral channel span and finite-support relation module whose omitted-channel rows provide a unit-pivot basis.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos249/PaperCompleteR8/KernelRelationBasis.lean#L1-L80

import Definitions.Def_Erdos249257_TotientKernelIndex
import Definitions.Def_Erdos249257_TotientKernelConditional
import Definitions.Def_Erdos249257_TotientMahlerDefect_v2
import Definitions.Def_Erdos249257_AllBaseTotientKernel_v2
import Definitions.Def_ErdosProblems_Erdos249_PaperCompleteR7_KernelIntegral_v2
import Definitions.Def_ErdosProblems_Erdos249_PaperCompleteR8_UnitPivotBasis_v2
import Mathlib
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Totient
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.PrimesCongruentOne

namespace Erdos257PeriodNoncollapse
end Erdos257PeriodNoncollapse

set_option autoImplicit false

/-!
# The integral relation-module basis missing from the paper

New r8 proof source. The r7 coordinate basis is reused unchanged. The map below
has the free Z-module on ALL channels as its domain and the actual integral
span as its codomain. Its kernel has the unit-pivot basis, not just a spanning
set. Maximal reductions are identified by uniqueness of canonical coordinates.

Pinned Mathlib source comments identify
APIs opened at 5e932f97dd25535344f80f9dd8da3aab83df0fe6.
-/

namespace ErdosProblems.Erdos249.PaperCompleteR8

open scoped BigOperators
open Erdos257PeriodNoncollapse
open ErdosProblems.Erdos249.PaperCompleteR7

abbrev IntegralChannelSpan (k e : ℕ) :=
  Submodule.span ℤ (Set.range (Erdos249257.allBaseThroughLevelFamily k e))

/-- The literal retained channel indices, not an arbitrary preimage of a
sequence that might also be represented by an omitted channel. -/
def retainedChannel (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    Erdos249257.AllBaseCanonicalIndex k e → Erdos249257.AllBaseThroughLevelIndex k e
  | Sum.inl i =>
      ⟨⟨i.val, by have hi := i.isLt; omega⟩,
        ⟨0, pow_pos (by omega : 0 < k) _⟩⟩
  | Sum.inr x =>
      ⟨⟨x.1.val + 1, by have hx := x.1.isLt; omega⟩,
        ⟨Erdos249257.allBaseCanonicalResidue k x, Erdos249257.allBaseCanonicalResidue_lt k hk x⟩⟩

theorem retainedChannel_value (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e)
    (j : Erdos249257.AllBaseCanonicalIndex k e) :
    Erdos249257.allBaseThroughLevelFamily k e (retainedChannel k e hk he j) =
      Erdos249257.allBaseCanonicalFamily k e j := by
  cases j with
  | inl j => rfl
  | inr j => rfl

/-- Finite normal coefficients, supplied by the already-proved integral
spanning theorem. Independence makes them unique; no rational rounding occurs. -/
noncomputable def integralNormalCoefficients (k e : ℕ) (hk : 2 ≤ k)
    (i : Erdos249257.AllBaseThroughLevelIndex k e) : Erdos249257.AllBaseCanonicalIndex k e →₀ ℤ :=
  Classical.choose
    (Finsupp.mem_span_range_iff_exists_finsupp.mp
      (allBaseTotientKernelSeq_mem_int_span k e hk i.1.val
        (Nat.le_of_lt_succ i.1.isLt) i.2.val i.2.isLt))

theorem integralNormalCoefficients_spec (k e : ℕ) (hk : 2 ≤ k)
    (i : Erdos249257.AllBaseThroughLevelIndex k e) :
    Finsupp.linearCombination ℤ (Erdos249257.allBaseCanonicalFamily k e)
      (integralNormalCoefficients k e hk i) = Erdos249257.allBaseThroughLevelFamily k e i := by
  exact Classical.choose_spec
    (Finsupp.mem_span_range_iff_exists_finsupp.mp
      (allBaseTotientKernelSeq_mem_int_span k e hk i.1.val
        (Nat.le_of_lt_succ i.1.isLt) i.2.val i.2.isLt))

/-- The unit-pivot system takes values in the integral span itself. -/
noncomputable def integralRelationSystem (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    UnitPivot.System ℤ (Erdos249257.AllBaseThroughLevelIndex k e)
      (Erdos249257.AllBaseCanonicalIndex k e) (IntegralChannelSpan k e) where
  value i := ⟨Erdos249257.allBaseThroughLevelFamily k e i, Submodule.subset_span ⟨i, rfl⟩⟩
  keep := retainedChannel k e hk he
  independent := by
    -- Mathlib/LinearAlgebra/LinearIndependent/Defs.lean: of_comp.
    apply LinearIndependent.of_comp (IntegralChannelSpan k e).subtype
    have hfun :
        (fun j => Erdos249257.allBaseThroughLevelFamily k e (retainedChannel k e hk he j)) =
          Erdos249257.allBaseCanonicalFamily k e := funext (retainedChannel_value k e hk he)
    change LinearIndependent ℤ
      (fun j => Erdos249257.allBaseThroughLevelFamily k e (retainedChannel k e hk he j))
    rw [hfun]
    exact int_linearIndependent_allBaseCanonicalFamily k e hk
  coeff := integralNormalCoefficients k e hk
  reconstruct := by
    intro i
    apply Subtype.ext
    -- Mathlib/LinearAlgebra/Finsupp/LinearCombination.lean:
    -- Finsupp.apply_linearCombination transports the subtype map through a sum.
    change (IntegralChannelSpan k e).subtype
      (Finsupp.linearCombination ℤ
        (fun j => (⟨Erdos249257.allBaseThroughLevelFamily k e (retainedChannel k e hk he j),
          Submodule.subset_span ⟨retainedChannel k e hk he j, rfl⟩⟩ :
            IntegralChannelSpan k e)) (integralNormalCoefficients k e hk i)) = _
    rw [Finsupp.apply_linearCombination]
    have hfun :
        (fun j => Erdos249257.allBaseThroughLevelFamily k e (retainedChannel k e hk he j)) =
          Erdos249257.allBaseCanonicalFamily k e := funext (retainedChannel_value k e hk he)
    change Finsupp.linearCombination ℤ
      (fun j => Erdos249257.allBaseThroughLevelFamily k e (retainedChannel k e hk he j))
        (integralNormalCoefficients k e hk i) = Erdos249257.allBaseThroughLevelFamily k e i
    rw [hfun]
    exact integralNormalCoefficients_spec k e hk i

noncomputable def integralChannelEvaluation (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :=
  (integralRelationSystem k e hk he).evaluation

noncomputable abbrev IntegralRelations (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :=
  LinearMap.ker (integralChannelEvaluation k e hk he)

abbrev OmittedIntegralChannel (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :=
  (integralRelationSystem k e hk he).Omitted

/-- The requested relation basis, with one vector for each omitted channel. -/
noncomputable def integralRelationBasis (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    Module.Basis (OmittedIntegralChannel k e hk he) ℤ (IntegralRelations k e hk he) :=
  (integralRelationSystem k e hk he).relationBasis













/-! ## Identification with the literal elementary reductions on the page -/


























end ErdosProblems.Erdos249.PaperCompleteR8


