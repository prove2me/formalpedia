-- Prove2me | Theorems.Thm_ErdosProblems_Erdos249_PaperCompleteR7_paper_maximal_power_reduction
-- name    : ErdosProblems.Erdos249.PaperCompleteR7.paper_maximal_power_reduction
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T13:54:12.084752+00:00
-- url     : https://prove2.me/theorems/7acb324f-5ecb-463a-9f79-cfce6b0cfb56
-- title:
--   Paper-coordinate power-residue reduction
-- statement:
--   For $k ≥ 2$ and $1 ≤ t < j$, the level-$j$ totient section at residue $k^t u$ reduces to the level-$(j-t)$ section with scalar $k^t$ times the missing-prime Euler product. No maximality assumption is required by this formal statement.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos249/PaperCompleteR7/KernelIntegral.lean#L224-L231

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

theorem ErdosProblems.Erdos249.PaperCompleteR7.paper_maximal_power_reduction (k j t u : ℕ) (hk : 2 ≤ k)
    (ht : 1 ≤ t) (htj : t < j) :
    Erdos249257.allBaseTotientKernelSeq k j (k ^ t * u) =
      ((k : ℚ) ^ t * missingEulerProduct k u) • Erdos249257.allBaseTotientKernelSeq k (j - t) u := by sorry
