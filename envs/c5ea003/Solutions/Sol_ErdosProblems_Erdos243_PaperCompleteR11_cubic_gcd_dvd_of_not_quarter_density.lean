-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.cubic_gcd_dvd_of_not_quarter_density
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:37:36.054249+00:00
-- url     : https://prove2.me/submissions/6e4624de-68d9-4fed-8be8-db88de4ffd2d

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_clean_windows_of_not_lower_density
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_common_divisor_dvd_cubic_third_difference
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_natural_orbit_common_divisor_tail
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
theorem solution (a C D : ℕ → ℕ) (P : ℕ → ℚ)
    (q A B : ℤ)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hclear : ∀ k : ℕ, (q : ℚ) * P k =
      (A : ℚ) * (k : ℚ) * ((k : ℚ) + 1) * ((k : ℚ) + 2) + (B : ℚ))
    (hlow : ¬ LowerDensityAtLeast {n : ℕ | (C n : ℚ) ≠ P n} (1 / 4)) :
    ∀ s : ℕ, (Nat.gcd (C s) (D s) : ℤ) ∣ 6 * A := by
  intro s
  obtain ⟨n, hsn, hn⟩ := clean_windows_of_not_lower_density
    {n : ℕ | (C n : ℚ) ≠ P n} 4 (by decide) hlow s
  have hagree : ∀ j : ℕ, j < 4 → (C (n + j) : ℚ) = P (n + j) := by
    intro j hj
    exact not_ne_iff.mp (hn j hj)
  apply common_divisor_dvd_cubic_third_difference C P q A B n
    (Nat.gcd (C s) (D s)) hclear hagree
  intro j _
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (show s ≤ n + j by omega)
  have h := natural_orbit_common_divisor_tail a C D hC hD s
    (Nat.gcd (C s) (D s)) (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _) k
  simpa only [← hk] using h.1
