-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.natural_orbit_common_divisor_tail
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:31:17.45236+00:00
-- url     : https://prove2.me/submissions/33f076f5-0ab4-4fdc-8c88-73b9226ee6fd

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
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
theorem solution (a C D : ℕ → ℕ)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (s d : ℕ) (hdC : d ∣ C s) (hdD : d ∣ D s) :
    ∀ k : ℕ, d ∣ C (s + k) ∧ d ∣ D (s + k) := by
  intro k
  induction k with
  | zero => simpa using And.intro hdC hdD
  | succ k ih =>
      constructor
      · have hs : d ∣ C (s + k + 1) + D (s + k) := by
          rw [hC]
          exact dvd_mul_of_dvd_right ih.1 _
        simpa only [Nat.add_assoc] using (Nat.dvd_add_iff_left ih.2).mpr hs
      · rw [show s + (k + 1) = s + k + 1 by omega, hD]
        exact dvd_mul_of_dvd_right ih.2 _
