-- Prove2me | Definitions.Def_ErdosProblems_Erdos249_PaperCompleteR8_FullKernelAssemblies_v2
-- name    : ErdosProblems_Erdos249_PaperCompleteR8_FullKernelAssemblies_v2
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-28T18:49:33.706225+00:00
-- url     : https://prove2.me/theorems/9db5d1ed-555d-4255-9753-0a1666bacd14
-- title:
--   Full dyadic and integral kernel assemblies
-- statement:
--   Defines the finite-support full-kernel and relation-module coordinates used in the displayed dyadic and all-base basis theorems.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos249/PaperCompleteR8/FullKernelAssemblies.lean#L1-L80

import Definitions.Def_Erdos249257_TotientKernelIndex
import Definitions.Def_Erdos249257_TotientKernelConditional
import Definitions.Def_Erdos249257_TotientMahlerDefect_v2
import Definitions.Def_Erdos249257_AllBaseTotientKernel_v2
import Definitions.Def_ErdosProblems_Erdos249_PaperCompleteR7_KernelIntegral_v2
import Definitions.Def_ErdosProblems_Erdos249_PaperCompleteR8_UnitPivotBasis_v2
import Definitions.Def_ErdosProblems_Erdos249_PaperCompleteR8_KernelRelationBasis_v2
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
# Full displayed basis statements

All finite-level arithmetic and the full odd-core independence theorem are
inherited from the repaired library. No new CRT or limiting assertion is
assumed. The full relation module uses finite-support coefficient vectors;
this is what makes passage to the union of all levels precise.

Mathlib API (pinned source opened):
* LinearAlgebra/Basis/Basic.lean: Module.Basis.span, coe_span_apply.
* Algebra/Module/Submodule/Equiv.lean: LinearEquiv.coe_ofEq_apply.
* LinearAlgebra/Finsupp/LinearCombination.lean: linearCombination_single,
  mem_span_range_iff_exists_finsupp.
* LinearAlgebra/LinearIndependent/Defs.lean: independence is injectivity
  of finite-support evaluation.

Build status belongs to source-bound validation receipts.
-/

namespace ErdosProblems.Erdos249.PaperCompleteR8

open scoped BigOperators
open Erdos257PeriodNoncollapse
open ErdosProblems.Erdos249.PaperCompleteR7






/-- The literal embedding of the odd-core indices in the infinite kernel. -/
def fullRetainedChannel : Erdos249257.TotientOddCoreIndex → Erdos249257.TotientDyadicKernelIndex
  | Sum.inl i => ⟨i.val, ⟨0, by positivity⟩⟩
  | Sum.inr ⟨j, r⟩ => ⟨j + 1, ⟨2 * r.val + 1, by
      have hr := r.isLt
      rw [pow_succ]
      omega⟩⟩

theorem fullRetainedChannel_value (i : Erdos249257.TotientOddCoreIndex) :
    Erdos249257.fullTotientKernelFamily (fullRetainedChannel i) = Erdos249257.oddCoreTotientKernelFamily i := by
  cases i with
  | inl i => rfl
  | inr i => cases i; rfl

noncomputable def fullNormalCoefficients (i : Erdos249257.TotientDyadicKernelIndex) :
    Erdos249257.TotientOddCoreIndex →₀ ℚ :=
  Classical.choose (Finsupp.mem_span_range_iff_exists_finsupp.mp
    (Erdos249257.totientKernelSeq_mem_span_oddCore i.1 i.2.val i.2.isLt))

theorem fullNormalCoefficients_spec (i : Erdos249257.TotientDyadicKernelIndex) :
    Finsupp.linearCombination ℚ Erdos249257.oddCoreTotientKernelFamily (fullNormalCoefficients i) =
      Erdos249257.fullTotientKernelFamily i :=
  Classical.choose_spec (Finsupp.mem_span_range_iff_exists_finsupp.mp
    (Erdos249257.totientKernelSeq_mem_span_oddCore i.1 i.2.val i.2.isLt))

noncomputable def fullRelationSystem :
    UnitPivot.System ℚ Erdos249257.TotientDyadicKernelIndex Erdos249257.TotientOddCoreIndex (ℕ → ℚ) where
  value := Erdos249257.fullTotientKernelFamily
  keep := fullRetainedChannel
  independent := by
    have h : (fun j => Erdos249257.fullTotientKernelFamily (fullRetainedChannel j)) =
        Erdos249257.oddCoreTotientKernelFamily := funext fullRetainedChannel_value
    rw [h]
    exact Erdos249257.linearIndependent_oddCoreTotientKernelFamily
  coeff := fullNormalCoefficients
  reconstruct := by
    intro i
    have h : (fun j => Erdos249257.fullTotientKernelFamily (fullRetainedChannel j)) =
        Erdos249257.oddCoreTotientKernelFamily := funext fullRetainedChannel_value
    rw [h]
    exact fullNormalCoefficients_spec i

noncomputable abbrev FullRelations := LinearMap.ker fullRelationSystem.evaluation
abbrev FullOmitted := fullRelationSystem.Omitted

noncomputable def fullRelationBasis : Module.Basis FullOmitted ℚ FullRelations :=
  fullRelationSystem.relationBasis

/-- Convert the base-two version of the all-base canonical index to the
existing odd-core index. The redundant Fin(1) digit is forced to zero. -/
def twoCanonicalToOddCore (e : ℕ) : Erdos249257.AllBaseCanonicalIndex 2 e → Erdos249257.TotientOddCoreIndex
  | Sum.inl i => Sum.inl i
  | Sum.inr x => Sum.inr ⟨x.1.val, x.2.1⟩












end ErdosProblems.Erdos249.PaperCompleteR8


