-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.primitive_cubic_constant_divisor_density
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:24:54.295986+00:00
-- url     : https://prove2.me/submissions/dcef8146-06c7-448b-b947-3e507ce90af0

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_primitive_periodic_pair_density
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_risingBinomial_pair_dvd_six_multiple
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
theorem solution (u : ℕ → ℕ) (m c : ℤ)
    (T d : ℕ) (hd : 2 ≤ d) (hdc : (d : ℤ) ∣ c)
    (hcop : ∀ n, T ≤ n → Nat.Coprime (u n) (u (n + 1))) :
    LowerDensityAtLeast {n : ℕ | (u n : ℤ) ≠ m * risingBinomial n + c}
      (1 / ((6 * d : ℕ) : ℝ)) := by
  apply primitive_periodic_pair_density u (fun n ↦ m * risingBinomial n + c)
    T d (6 * d) hd (by omega) hcop
  intro n k hphase
  obtain ⟨h0, h1⟩ := risingBinomial_pair_dvd_six_multiple d n k hphase
  exact ⟨dvd_add (dvd_mul_of_dvd_right h0 m) hdc,
    dvd_add (dvd_mul_of_dvd_right h1 m) hdc⟩
