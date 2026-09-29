-- Prove2me | Theorems.Thm_ErdosProblems_Erdos249_PaperCompleteR7_allBase_power_residue_euler
-- name    : ErdosProblems.Erdos249.PaperCompleteR7.allBase_power_residue_euler
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T13:53:55.775403+00:00
-- url     : https://prove2.me/theorems/4457bc08-2e42-4622-bcb9-7a317a898a46
-- title:
--   Power-residue reduction of all-base totient sections
-- statement:
--   For $k ≥ 2$ and $h,t ≥ 1$, the section at level $h+t$ and residue $k^t u$ is a scalar multiple of the level-$h$ section at residue $u$. The scalar is $k^t$ times the missing-prime Euler product.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos249/PaperCompleteR7/KernelIntegral.lean#L194-L222

import Definitions.Def_Erdos249257_TotientKernelIndex
import Definitions.Def_Erdos249257_TotientKernelConditional
import Definitions.Def_Erdos249257_TotientMahlerDefect
import Definitions.Def_Erdos249257_AllBaseTotientKernel
import Definitions.Def_ErdosProblems_Erdos249_PaperCompleteR7_KernelIntegral
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


open scoped BigOperators
open Erdos257PeriodNoncollapse

















/-! ## The exact Euler-product multiplier on the page -/

open ErdosProblems.Erdos249.PaperCompleteR7

theorem ErdosProblems.Erdos249.PaperCompleteR7.allBase_power_residue_euler (k h t u : ℕ) (hk : 2 ≤ k)
    (hh : 1 ≤ h) (ht : 1 ≤ t) :
    Erdos249257.allBaseTotientKernelSeq k (h + t) (k ^ t * u) =
      ((k : ℚ) ^ t * missingEulerProduct k u) • Erdos249257.allBaseTotientKernelSeq k h u := by sorry
