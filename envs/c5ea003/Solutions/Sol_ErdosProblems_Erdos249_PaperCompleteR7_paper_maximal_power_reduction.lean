-- Prove2me | solution 1 for ErdosProblems.Erdos249.PaperCompleteR7.paper_maximal_power_reduction
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T14:03:00.973258+00:00
-- url     : https://prove2.me/submissions/8db3cb2d-3804-4b00-8dda-df7abe597f0c

import Definitions.Def_Erdos249257_TotientKernelIndex
import Definitions.Def_Erdos249257_TotientKernelConditional
import Definitions.Def_Erdos249257_TotientMahlerDefect
import Definitions.Def_Erdos249257_AllBaseTotientKernel
import Definitions.Def_ErdosProblems_Erdos249_PaperCompleteR7_KernelIntegral
import Theorems.Thm_ErdosProblems_Erdos249_PaperCompleteR7_allBase_power_residue_euler
import Mathlib
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Totient
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.PrimesCongruentOne

/-!
# Integral coordinates and the paper's Euler-product scalar

Targets: thm:kkernelrank and the integral-basis clause of
cor:integral-normal-form. The rational basis is reused without reproving its
CRT independence theorem. Its integral span is proved separately: rational
spanning alone would not establish the assertion over Z.

Build status: complete proof-source candidates; NOT COMPILED in this return.
The assertion that the named relation rows form a basis is NOT hidden inside
this file's integral coordinate theorem. Its remaining integration is recorded
separately in the coverage file.
-/

namespace ErdosProblems.Erdos249.PaperCompleteR7
open scoped BigOperators
open Erdos257PeriodNoncollapse

















/-! ## The exact Euler-product multiplier on the page -/
end ErdosProblems.Erdos249.PaperCompleteR7

open scoped BigOperators
open Erdos257PeriodNoncollapse
open ErdosProblems in
open ErdosProblems.Erdos249 in
open ErdosProblems.Erdos249.PaperCompleteR7 in
theorem solution (k j t u : ℕ) (hk : 2 ≤ k)
    (ht : 1 ≤ t) (htj : t < j) :
    Erdos249257.allBaseTotientKernelSeq k j (k ^ t * u) =
      ((k : ℚ) ^ t * missingEulerProduct k u) • Erdos249257.allBaseTotientKernelSeq k (j - t) u := by
  simpa only [Nat.sub_add_cancel (Nat.le_of_lt htj)] using
    allBase_power_residue_euler k (j - t) t u hk (by omega) ht
