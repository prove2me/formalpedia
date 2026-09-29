-- Prove2me | solution 1 for ErdosProblems.Erdos249.PaperCompleteR7.stepScalar_eulerProduct
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T13:57:10.816911+00:00
-- url     : https://prove2.me/submissions/07dea2b4-0b15-4663-88e7-c86c9ea03be5

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
theorem solution (k u : ℕ) (hk : 0 < k) :
    ((Nat.totient k * Nat.gcd k u : ℕ) : ℚ) /
        (Nat.totient (Nat.gcd k u) : ℚ) =
      (k : ℚ) * missingEulerProduct k u := by
  classical
  let g := Nat.gcd k u
  let A := k.primeFactors.filter (fun p => p ∣ u)
  let B := k.primeFactors.filter (fun p => ¬ p ∣ u)
  have hg : 0 < g := Nat.gcd_pos_of_pos_left u hk
  have hA : g.primeFactors = A := by
    ext p
    simp only [Nat.mem_primeFactors, Finset.mem_filter, A, g]
    constructor
    · rintro ⟨hp, hpg, hgn⟩
      exact ⟨⟨hp, hpg.trans (Nat.gcd_dvd_left k u), hk.ne'⟩,
        hpg.trans (Nat.gcd_dvd_right k u)⟩
    · rintro ⟨⟨hp, hpk, hkn⟩, hpu⟩
      exact ⟨hp, Nat.dvd_gcd hpk hpu, hg.ne'⟩
  have hdisj : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro p hpa hpb
    exact (Finset.mem_filter.mp hpb).2 (Finset.mem_filter.mp hpa).2
  have hunion : A ∪ B = k.primeFactors := by
    ext p
    simp only [Finset.mem_union, Finset.mem_filter, A, B]
    tauto
  have hprod : (∏ p ∈ k.primeFactors, (1 - (p : ℚ)⁻¹)) =
      (∏ p ∈ A, (1 - (p : ℚ)⁻¹)) * (∏ p ∈ B, (1 - (p : ℚ)⁻¹)) := by
    rw [← hunion, Finset.prod_union hdisj]
  have hkphi := Nat.totient_eq_mul_prod_factors k
  have hgphi := Nat.totient_eq_mul_prod_factors g
  rw [hprod] at hkphi
  rw [hA] at hgphi
  have hφg : (Nat.totient g : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hg).ne'
  change ((Nat.totient k * g : ℕ) : ℚ) / (Nat.totient g : ℚ) = _
  apply (div_eq_iff hφg).2
  push_cast
  change (Nat.totient k : ℚ) * (g : ℚ) =
    ((k : ℚ) * (∏ p ∈ B, (1 - (p : ℚ)⁻¹))) * (Nat.totient g : ℚ)
  rw [hkphi, hgphi]
  ring
