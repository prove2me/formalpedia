-- Prove2me | solution 1 for ErdosProblems.Erdos249.PaperCompleteR7.allBase_power_residue_euler
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T14:00:12.438291+00:00
-- url     : https://prove2.me/submissions/0361cc21-ac15-42fa-a143-2f31d827c714

import Definitions.Def_Erdos249257_TotientKernelIndex
import Definitions.Def_Erdos249257_TotientKernelConditional
import Definitions.Def_Erdos249257_TotientMahlerDefect
import Definitions.Def_Erdos249257_AllBaseTotientKernel
import Definitions.Def_ErdosProblems_Erdos249_PaperCompleteR7_KernelIntegral
import Theorems.Thm_ErdosProblems_Erdos249_PaperCompleteR7_stepScalar_eulerProduct
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
theorem solution (k h t u : ℕ) (hk : 2 ≤ k)
    (hh : 1 ≤ h) (ht : 1 ≤ t) :
    Erdos249257.allBaseTotientKernelSeq k (h + t) (k ^ t * u) =
      ((k : ℚ) ^ t * missingEulerProduct k u) • Erdos249257.allBaseTotientKernelSeq k h u := by
  have hkpos : 0 < k := by omega
  have hstep := Erdos249257.allBaseTotientKernel_step k hkpos h u hh
  rw [stepScalar_eulerProduct k u hkpos] at hstep
  have hpow : (k : ℚ) ^ (t - 1) * (k : ℚ) = (k : ℚ) ^ t := by
    rw [← pow_succ, Nat.sub_add_cancel ht]
  ext n
  have harg : k ^ (h + t) * n + k ^ t * u = k ^ t * (k ^ h * n + u) := by
    rw [pow_add]
    ring
  have hp := Erdos249257.allBase_totient_pow_mul_eq k hkpos (k ^ h * n + u) t ht
  have hs := congrFun hstep n
  have harg1 : k ^ (h + 1) * n + k * u = k * (k ^ h * n + u) := by ring
  simp only [Erdos249257.allBaseTotientKernelSeq, Pi.smul_apply, smul_eq_mul, harg1] at hs
  simp only [Erdos249257.allBaseTotientKernelSeq, Pi.smul_apply, smul_eq_mul, harg]
  rw [hp]
  push_cast
  rw [hs]
  calc
    (k : ℚ) ^ (t - 1) * ((k : ℚ) * missingEulerProduct k u *
        (Nat.totient (k ^ h * n + u) : ℚ)) =
      ((k : ℚ) ^ (t - 1) * k) * missingEulerProduct k u *
        (Nat.totient (k ^ h * n + u) : ℚ) := by ring
    _ = _ := by rw [hpow]
