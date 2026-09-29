-- Prove2me | Definitions.Def_ErdosProblems_Erdos249_PaperCompleteR7_KernelIntegral
-- name    : ErdosProblems_Erdos249_PaperCompleteR7_KernelIntegral
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T13:52:55.545482+00:00
-- url     : https://prove2.me/theorems/f7c2537e-3aaf-43ff-8535-226655849e31
-- title:
--   Integral totient kernel coordinates and reduction scalar
-- statement:
--   Defines an integer reduction multiplier and the Euler product factor used for composite-base totient sections, alongside integral spanning and independence results.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos249/PaperCompleteR7/KernelIntegral.lean#L24-L28
--   Supporting source declaration: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos249/PaperCompleteR7/KernelIntegral.lean#L122-L151

import Definitions.Def_Erdos249257_TotientKernelIndex
import Definitions.Def_Erdos249257_TotientKernelConditional
import Definitions.Def_Erdos249257_TotientMahlerDefect
import Definitions.Def_Erdos249257_AllBaseTotientKernel
import Mathlib
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Totient
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.PrimesCongruentOne

namespace Erdos257PeriodNoncollapse
end Erdos257PeriodNoncollapse

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

/-- The product is over primes dividing k but not dividing u. -/
def missingEulerProduct (k u : ℕ) : ℚ :=
  ∏ p ∈ k.primeFactors.filter (fun p => ¬ p ∣ u), (1 - (p : ℚ)⁻¹)







end ErdosProblems.Erdos249.PaperCompleteR7


