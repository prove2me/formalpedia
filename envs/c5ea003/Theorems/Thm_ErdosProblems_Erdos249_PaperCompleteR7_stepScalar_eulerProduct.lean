-- Prove2me | Theorems.Thm_ErdosProblems_Erdos249_PaperCompleteR7_stepScalar_eulerProduct
-- name    : ErdosProblems.Erdos249.PaperCompleteR7.stepScalar_eulerProduct
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T13:54:11.300256+00:00
-- url     : https://prove2.me/theorems/37d2b979-8c1c-4f73-a4ca-a5e61f1ac711
-- title:
--   Euler product formula for the one-step reduction scalar
-- statement:
--   For $k > 0$, the totient-and-gcd reduction scalar equals $k$ times the Euler product over primes dividing $k$ but not the residue $u$.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos249/PaperCompleteR7/KernelIntegral.lean#L150-L192

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

theorem ErdosProblems.Erdos249.PaperCompleteR7.stepScalar_eulerProduct (k u : ℕ) (hk : 0 < k) :
    ((Nat.totient k * Nat.gcd k u : ℕ) : ℚ) /
        (Nat.totient (Nat.gcd k u) : ℚ) =
      (k : ℚ) * missingEulerProduct k u := by sorry
