-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.constant_gcd_natural_quotient_tail
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:27:40.613363+00:00
-- url     : https://prove2.me/submissions/28084534-dcf8-4502-886f-2ee353714edc

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
# Constructed primitive cubic tails below quarter density

The stabilising divisor, the exact
natural quotient recurrence, the integral profile coefficients, and their
Bezout certificate are produced from the original orbit. The index is never
reset: division by a fixed gcd does not replace n by n-N in the polynomial.

This eliminates a normalisation supplier, but does NOT prove that the primitive
constant is a unit. Integral primitive profiles with other constants remain in
the universal-density problem.
-/

open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution
    (a C D : ℕ → ℕ) (N g : ℕ) (hg : 0 < g)
    (hCpos : ∀ n, 0 < C n) (hDpos : ∀ n, 0 < D n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hG : ∀ n, N ≤ n → Nat.gcd (C n) (D n) = g) :
    ∀ n, N ≤ n →
      g ∣ C n ∧ g ∣ D n ∧ 0 < C n / g ∧ 0 < D n / g ∧
      Nat.Coprime (C n / g) (D n / g) ∧
      C (n + 1) / g + D n / g = a n * (C n / g) ∧
      D (n + 1) / g = a n * (D n / g) := by
  have hgC : ∀ n, N ≤ n → g ∣ C n := by
    intro n hn
    rw [← hG n hn]
    exact Nat.gcd_dvd_left _ _
  have hgD : ∀ n, N ≤ n → g ∣ D n := by
    intro n hn
    rw [← hG n hn]
    exact Nat.gcd_dvd_right _ _
  intro n hn
  have hcop := Nat.coprime_div_gcd_div_gcd
    (Nat.gcd_pos_of_pos_left (D n) (hCpos n))
  rw [hG n hn] at hcop
  refine ⟨hgC n hn, hgD n hn,
    Nat.div_pos (Nat.le_of_dvd (hCpos n) (hgC n hn)) hg,
    Nat.div_pos (Nat.le_of_dvd (hDpos n) (hgD n hn)) hg, hcop, ?_, ?_⟩
  · apply Nat.eq_of_mul_eq_mul_left hg
    calc
      g * (C (n + 1) / g + D n / g) = C (n + 1) + D n := by
        rw [Nat.mul_add, Nat.mul_div_cancel' (hgC (n + 1) (by omega)),
          Nat.mul_div_cancel' (hgD n hn)]
      _ = a n * C n := hC n
      _ = g * (a n * (C n / g)) := by
        rw [mul_left_comm, Nat.mul_div_cancel' (hgC n hn)]
  · rw [hD n]
    exact Nat.mul_div_assoc (a n) (hgD n hn)
