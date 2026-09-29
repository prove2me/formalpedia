-- Prove2me | Definitions.Def_ErdosProblems_Erdos249_PaperCompleteR7_KernelIntegral_v2
-- name    : ErdosProblems_Erdos249_PaperCompleteR7_KernelIntegral_v2
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-28T01:45:51.893802+00:00
-- url     : https://prove2.me/theorems/e90d604a-7b6f-45ea-aa08-f1c24ae84eec
-- title:
--   Integral totient kernel coordinates and reduction scalar
-- statement:
--   Defines an integer reduction multiplier and the Euler product factor used for composite-base totient sections, alongside integral spanning and independence results.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos249/PaperCompleteR7/KernelIntegral.lean#L24-L28
--   Supporting source declaration: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos249/PaperCompleteR7/KernelIntegral.lean#L122-L151

import Definitions.Def_Erdos249257_TotientKernelIndex
import Definitions.Def_Erdos249257_TotientKernelConditional
import Definitions.Def_Erdos249257_TotientMahlerDefect_v2
import Definitions.Def_Erdos249257_AllBaseTotientKernel_v2
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

/-- The integer multiplier in a one-step composite-base reduction. -/
def integralStepScalar (k u : ℕ) : ℕ :=
  (Nat.totient k / Nat.totient (Nat.gcd k u)) * Nat.gcd k u

/-- Divisibility of totients makes the rational-looking scalar integral. -/
theorem stepScalar_cast (k u : ℕ) (hk : 0 < k) :
    (integralStepScalar k u : ℚ) =
      ((Nat.totient k * Nat.gcd k u : ℕ) : ℚ) /
        (Nat.totient (Nat.gcd k u) : ℚ) := by
  have hd := Nat.totient_dvd_of_dvd (Nat.gcd_dvd_left k u)
  have hg : 0 < Nat.totient (Nat.gcd k u) :=
    Nat.totient_pos.mpr (Nat.gcd_pos_of_pos_left u hk)
  have hgQ : (Nat.totient (Nat.gcd k u) : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  have hn := Nat.div_mul_cancel hd
  have hnQ : ((Nat.totient k / Nat.totient (Nat.gcd k u) : ℕ) : ℚ) *
      (Nat.totient (Nat.gcd k u) : ℚ) = (Nat.totient k : ℚ) := by
    exact_mod_cast hn
  unfold integralStepScalar
  push_cast
  apply (eq_div_iff hgQ).mpr
  calc
    _ = (((Nat.totient k / Nat.totient (Nat.gcd k u) : ℕ) : ℚ) *
          (Nat.totient (Nat.gcd k u) : ℚ)) * (Nat.gcd k u : ℚ) := by ring
    _ = _ := by rw [hnQ]

/-- Z-module form of the existing rational one-step relation. -/
theorem allBase_step_integral (k : ℕ) (hk : 0 < k) (h u : ℕ) (hh : 1 ≤ h) :
    Erdos249257.allBaseTotientKernelSeq k (h + 1) (k * u) =
      (integralStepScalar k u : ℤ) • Erdos249257.allBaseTotientKernelSeq k h u := by
  rw [Erdos249257.allBaseTotientKernel_step k hk h u hh, ← stepScalar_cast k u hk]
  ext n
  simp [Pi.smul_apply, zsmul_eq_mul]

/-- The zero-channel reduction also holds over the integers. -/
theorem allBase_zero_integral (k : ℕ) (hk : 0 < k) (j : ℕ) :
    Erdos249257.allBaseTotientKernelSeq k (j + 1) 0 =
      (k ^ j : ℤ) • Erdos249257.allBaseTotientKernelSeq k 1 0 := by
  rw [Erdos249257.allBaseTotientKernel_zero_residue k hk j]
  ext n
  simp [Pi.smul_apply, zsmul_eq_mul]

/-- Integer spanning, with no denominator-clearing premise. -/
theorem allBaseTotientKernelSeq_mem_int_span (k e : ℕ) (hk : 2 ≤ k) :
    ∀ j : ℕ, j ≤ e → ∀ r : ℕ, r < k ^ j →
      Erdos249257.allBaseTotientKernelSeq k j r ∈
        Submodule.span ℤ (Set.range (Erdos249257.allBaseCanonicalFamily k e)) := by
  have hkpos : 0 < k := by omega
  intro j
  induction j with
  | zero =>
      intro _ r hr
      have hr0 : r = 0 := by simpa using hr
      subst r
      exact Submodule.subset_span ⟨Sum.inl 0, rfl⟩
  | succ j ih =>
      intro hje r hr
      by_cases hr0 : r = 0
      · subst r
        rw [allBase_zero_integral k hkpos j]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl 1, rfl⟩)
      · by_cases hkr : k ∣ r
        · obtain ⟨u, rfl⟩ := hkr
          have hu0 : 0 < u := by
            rcases Nat.eq_zero_or_pos u with rfl | h
            · simp at hr0
            · exact h
          have hulk : u < k ^ j := by
            have hmul : k * u < k * k ^ j := by
              calc k * u < k ^ (j + 1) := hr
                _ = k * k ^ j := by ring
            exact lt_of_mul_lt_mul_left hmul (Nat.zero_le k)
          have hj1 : 1 ≤ j := by
            by_contra hcon
            have hj0 : j = 0 := by omega
            subst j
            simp only [pow_zero] at hulk
            omega
          rw [allBase_step_integral k hkpos j u hj1]
          exact Submodule.smul_mem _ _ (ih (by omega) u hulk)
        · have hjlt : j < e := by omega
          obtain ⟨s, u, hu_pos, hu_lt, rfl⟩ :
              ∃ s u, 0 < u ∧ u < k ∧ r = k * s + u := by
            refine ⟨r / k, r % k, ?_, Nat.mod_lt _ hkpos, (Nat.div_add_mod r k).symm⟩
            rcases Nat.eq_zero_or_pos (r % k) with h | h
            · exact absurd (Nat.dvd_of_mod_eq_zero h) hkr
            · exact h
          have hs_lt : s < k ^ j := by
            have hmul : k * s < k * k ^ j := by
              have hb : k * s + u < k * k ^ j := by
                calc k * s + u < k ^ (j + 1) := hr
                  _ = k * k ^ j := by ring
              omega
            exact lt_of_mul_lt_mul_left hmul (Nat.zero_le k)
          refine Submodule.subset_span
            ⟨Sum.inr ⟨⟨j, hjlt⟩, (⟨s, hs_lt⟩, ⟨u - 1, by omega⟩)⟩, ?_⟩
          simp only [Erdos249257.allBaseCanonicalFamily, Erdos249257.allBaseCanonicalResidue]
          congr 1
          omega

theorem int_span_allBaseThroughLevelFamily_eq (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    Submodule.span ℤ (Set.range (Erdos249257.allBaseThroughLevelFamily k e)) =
      Submodule.span ℤ (Set.range (Erdos249257.allBaseCanonicalFamily k e)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨⟨j, r⟩, rfl⟩
    exact allBaseTotientKernelSeq_mem_int_span k e hk j.val
      (Nat.le_of_lt_succ j.isLt) r.val r.isLt
  · exact Submodule.span_mono
      (Erdos249257.range_allBaseCanonicalFamily_subset_throughLevel k e hk he)

theorem int_linearIndependent_allBaseCanonicalFamily (k e : ℕ) (hk : 2 ≤ k) :
    LinearIndependent ℤ (Erdos249257.allBaseCanonicalFamily k e) :=
  (Erdos249257.linearIndependent_allBaseCanonicalFamily k e hk).restrict_scalars' ℤ

/-- An actual Z-basis, not merely a rational basis with integer generators. -/
noncomputable def integralTotientKernelBasis (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    Module.Basis (Erdos249257.AllBaseCanonicalIndex k e) ℤ
      (Submodule.span ℤ (Set.range (Erdos249257.allBaseThroughLevelFamily k e))) :=
  (Module.Basis.span (int_linearIndependent_allBaseCanonicalFamily k e hk)).map
    (LinearEquiv.ofEq _ _ (int_span_allBaseThroughLevelFamily_eq k e hk he).symm)

/-! ## The exact Euler-product multiplier on the page -/









end ErdosProblems.Erdos249.PaperCompleteR7


