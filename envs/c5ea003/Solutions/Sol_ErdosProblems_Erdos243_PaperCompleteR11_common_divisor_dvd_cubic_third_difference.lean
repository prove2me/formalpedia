-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.common_divisor_dvd_cubic_third_difference
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:33:56.598203+00:00
-- url     : https://prove2.me/submissions/cc839906-5299-46f6-ac26-40d2defbd0ba

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubic_four_agreements_difference
import Mathlib
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring

/-!
# A uniform four-window gcd reduction for cubic profiles

The reduction works below density `1/4`, not only
under density zero. Four agreeing values give the exact third difference;
every earlier common divisor divides that difference. No upper growth estimate,
record restart, denominator reduction, or prime-existence hypothesis is needed.
-/

open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution (C : ℕ → ℕ) (P : ℕ → ℚ)
    (q A B : ℤ) (n d : ℕ)
    (hclear : ∀ k : ℕ, (q : ℚ) * P k =
      (A : ℚ) * (k : ℚ) * ((k : ℚ) + 1) * ((k : ℚ) + 2) + (B : ℚ))
    (hagree : ∀ j : ℕ, j < 4 → (C (n + j) : ℚ) = P (n + j))
    (hdiv : ∀ j : ℕ, j < 4 → d ∣ C (n + j)) :
    (d : ℤ) ∣ 6 * A := by
  have hd0 : (d : ℤ) ∣ (C n : ℤ) := by
    have h := hdiv 0 (by decide)
    simp only [Nat.add_zero] at h
    exact_mod_cast h
  have hd1 : (d : ℤ) ∣ (C (n + 1) : ℤ) := by exact_mod_cast hdiv 1 (by decide)
  have hd2 : (d : ℤ) ∣ (C (n + 2) : ℤ) := by exact_mod_cast hdiv 2 (by decide)
  have hd3 : (d : ℤ) ∣ (C (n + 3) : ℤ) := by exact_mod_cast hdiv 3 (by decide)
  have hlin : (d : ℤ) ∣ ((C (n + 3) : ℤ) - 3 * (C (n + 2) : ℤ) +
      3 * (C (n + 1) : ℤ) - (C n : ℤ)) :=
    dvd_sub (dvd_add (dvd_sub hd3 (dvd_mul_of_dvd_right hd2 3))
      (dvd_mul_of_dvd_right hd1 3)) hd0
  have h := dvd_mul_of_dvd_right hlin q
  rwa [cubic_four_agreements_difference C P q A B n hclear hagree] at h
