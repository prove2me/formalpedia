-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.primitive_step_adjacent_coprime
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:30:10.629917+00:00
-- url     : https://prove2.me/submissions/1832df90-655a-46ac-8c92-d60f49975b5d

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
theorem solution (a u v u' : ℕ)
    (hstep : u' + v = a * u) (hcop : Nat.Coprime u v) :
    Nat.Coprime u u' := by
  rw [Nat.coprime_iff_gcd_eq_one]
  let d := Nat.gcd u u'
  have hdu : d ∣ u := Nat.gcd_dvd_left _ _
  have hdu' : d ∣ u' := Nat.gcd_dvd_right _ _
  have hsum : d ∣ u' + v := by
    rw [hstep]
    exact dvd_mul_of_dvd_right hdu a
  have hdv : d ∣ v := (Nat.dvd_add_iff_right hdu').mpr hsum
  have hd : d ∣ 1 := by
    simpa only [hcop.gcd_eq_one] using Nat.dvd_gcd hdu hdv
  exact Nat.dvd_one.mp hd
