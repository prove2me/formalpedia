-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.primitive_pair_profile_hit
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:45:33.241254+00:00
-- url     : https://prove2.me/submissions/233d182f-6389-4fa5-b3e9-cbb2b1e65349

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Mathlib
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring

/-!
# Nonunit constants: explicit primitive divisor obstructions

The old 1/(12*d) loss is unnecessary for a single
periodic family of disjoint two-windows. We obtain 1/(6*d) for every d >= 2,
and 1/d when d is coprime to 6. In particular divisors 2, 3, and any divisor
between 2 and 28 coprime to 6 give the universal 1/28 bound in this branch.
This does not discard constants whose prime factors are all >= 29.
-/

open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution (u : ℕ → ℕ) (P : ℕ → ℤ) (n d : ℕ)
    (hd : 2 ≤ d) (hcop : Nat.Coprime (u n) (u (n + 1)))
    (h0 : (d : ℤ) ∣ P n) (h1 : (d : ℤ) ∣ P (n + 1)) :
    ∃ i : ℕ, i < 2 ∧ (u (n + i) : ℤ) ≠ P (n + i) := by
  by_contra hbad
  have ha : ∀ i : ℕ, i < 2 → (u (n + i) : ℤ) = P (n + i) := by
    intro i hi
    by_contra hh
    exact hbad ⟨i, hi, hh⟩
  have ha0 : (u n : ℤ) = P n := by simpa using ha 0 (by decide)
  rw [← ha0] at h0
  rw [← ha 1 (by decide)] at h1
  have hu0 : d ∣ u n := by exact_mod_cast h0
  have hu1 : d ∣ u (n + 1) := by exact_mod_cast h1
  have hdu : d ∣ 1 := by
    simpa only [hcop.gcd_eq_one] using Nat.dvd_gcd hu0 hu1
  have := Nat.dvd_one.mp hdu
  omega
