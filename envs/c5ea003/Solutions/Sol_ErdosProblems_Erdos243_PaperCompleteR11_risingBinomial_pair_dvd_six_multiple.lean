-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.risingBinomial_pair_dvd_six_multiple
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:19:43.153508+00:00
-- url     : https://prove2.me/submissions/467b3466-15c9-4635-b3dd-3a5525f324a8

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_six_mul_risingBinomial
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
theorem solution (d n k : ℕ)
    (hphase : n + 1 = 6 * d * k) :
    (d : ℤ) ∣ risingBinomial n ∧ (d : ℤ) ∣ risingBinomial (n + 1) := by
  have hp : (n : ℤ) + 1 = 6 * (d : ℤ) * (k : ℤ) := by exact_mod_cast hphase
  constructor
  · refine ⟨(k : ℤ) * (n : ℤ) * ((n : ℤ) + 2), ?_⟩
    have h6 : 6 * risingBinomial n =
        6 * ((d : ℤ) * ((k : ℤ) * (n : ℤ) * ((n : ℤ) + 2))) := by
      rw [six_mul_risingBinomial, hp]
      ring
    omega
  · refine ⟨(k : ℤ) * ((n : ℤ) + 2) * ((n : ℤ) + 3), ?_⟩
    have h6 : 6 * risingBinomial (n + 1) =
        6 * ((d : ℤ) * ((k : ℤ) * ((n : ℤ) + 2) * ((n : ℤ) + 3))) := by
      rw [six_mul_risingBinomial]
      push_cast
      calc
        ((n : ℤ) + 1) * ((n : ℤ) + 1 + 1) * ((n : ℤ) + 1 + 2) =
            ((n : ℤ) + 1) * ((n : ℤ) + 2) * ((n : ℤ) + 3) := by ring
        _ = 6 * ((d : ℤ) * ((k : ℤ) * ((n : ℤ) + 2) * ((n : ℤ) + 3))) := by
          rw [hp]
          ring
    omega
