-- Prove2me | solution 1 for ErdosProblems.Erdos249.PaperCompleteR8.displayed_all_base_kernel
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T14:08:44.942506+00:00
-- url     : https://prove2.me/submissions/cd293c1b-9f8e-4640-905a-c2bf8b284a62

import Definitions.Def_Erdos249257_TotientKernelIndex
import Definitions.Def_Erdos249257_TotientKernelConditional
import Definitions.Def_Erdos249257_TotientMahlerDefect
import Definitions.Def_Erdos249257_AllBaseTotientKernel
import Definitions.Def_ErdosProblems_Erdos249_PaperCompleteR7_KernelIntegral
import Definitions.Def_ErdosProblems_Erdos249_PaperCompleteR8_UnitPivotBasis
import Theorems.Thm_Erdos249257_finrank_allBaseThroughLevelFamily_eq
import Theorems.Thm_ErdosProblems_Erdos249_PaperCompleteR7_paper_maximal_power_reduction
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

namespace ErdosProblems.Erdos249.PaperCompleteR8
end ErdosProblems.Erdos249.PaperCompleteR8

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
end ErdosProblems.Erdos249.PaperCompleteR8

open scoped BigOperators
open Erdos257PeriodNoncollapse
open ErdosProblems.Erdos249.PaperCompleteR7
open ErdosProblems in
open ErdosProblems.Erdos249 in
open ErdosProblems.Erdos249.PaperCompleteR8 in
theorem solution (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    Module.finrank ℚ (Submodule.span ℚ (Set.range (Erdos249257.allBaseThroughLevelFamily k e))) =
      k ^ e + 1 ∧
    (∃ b : Module.Basis (Erdos249257.AllBaseCanonicalIndex k e) ℚ
        (Submodule.span ℚ (Set.range (Erdos249257.allBaseThroughLevelFamily k e))),
      ∀ i, (b i : ℕ → ℚ) = Erdos249257.allBaseCanonicalFamily k e i) ∧
    (∀ j : ℕ, 1 ≤ j →
      Erdos249257.allBaseTotientKernelSeq k j 0 =
        (k ^ (j - 1) : ℚ) • Erdos249257.allBaseTotientKernelSeq k 1 0) ∧
    (∀ j t u : ℕ, 1 ≤ t → t < j →
      Erdos249257.allBaseTotientKernelSeq k j (k ^ t * u) =
        ((k : ℚ) ^ t * missingEulerProduct k u) •
          Erdos249257.allBaseTotientKernelSeq k (j - t) u) := by
  refine ⟨Erdos249257.finrank_allBaseThroughLevelFamily_eq k e hk he, ?_, ?_, ?_⟩
  · refine ⟨Erdos249257.allBaseTotientKernelBasis k e hk he, ?_⟩
    intro i
    simp only [Erdos249257.allBaseTotientKernelBasis, Module.Basis.map_apply,
      LinearEquiv.coe_ofEq_apply, Module.Basis.coe_span_apply]
  · intro j hj
    have h := Erdos249257.allBaseTotientKernel_zero_residue k (by omega : 0 < k) (j - 1)
    rw [Nat.sub_add_cancel hj] at h
    exact h
  · intro j t u ht htj
    exact paper_maximal_power_reduction k j t u hk ht htj
