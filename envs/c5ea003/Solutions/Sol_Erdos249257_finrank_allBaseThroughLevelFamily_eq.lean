-- Prove2me | solution 1 for Erdos249257.finrank_allBaseThroughLevelFamily_eq
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T13:57:09.775685+00:00
-- url     : https://prove2.me/submissions/461bedb4-a5f2-4e58-9e88-b4d75d5a2f2a

import Definitions.Def_Erdos249257_TotientKernelIndex
import Definitions.Def_Erdos249257_TotientKernelConditional
import Definitions.Def_Erdos249257_TotientMahlerDefect
import Definitions.Def_Erdos249257_AllBaseTotientKernel
import Theorems.Thm_Erdos249257_finrank_allBaseTotientKernel_eq_of_linearIndependent
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Totient
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.PrimesCongruentOne

namespace Erdos249257
open Module Matrix
/-- **The exact unconditional all-base rank**: for every integer base `k ≥ 2` and
every depth `e`, the canonical level-`e` totient kernel has dimension `k^e + 1`. -/
theorem finrank_allBaseTotientKernel_eq (k e : ℕ) (hk : 2 ≤ k) :
    finrank ℚ (Submodule.span ℚ (Set.range (allBaseCanonicalFamily k e))) =
      k ^ e + 1 :=
  finrank_allBaseTotientKernel_eq_of_linearIndependent k e hk
    (linearIndependent_allBaseCanonicalFamily k e hk)
end Erdos249257

open Erdos249257
open Module Matrix
open Erdos249257 in
theorem solution (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    finrank ℚ (Submodule.span ℚ (Set.range (allBaseThroughLevelFamily k e))) =
      k ^ e + 1 := by
  rw [span_allBaseThroughLevelFamily_eq k e hk he]
  exact finrank_allBaseTotientKernel_eq k e hk
