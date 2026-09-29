-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.cubic_gcd_stabilises_of_not_quarter_density
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:47:23.121683+00:00
-- url     : https://prove2.me/submissions/0424b203-1f69-4c15-9c94-879ff7eecb9c

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubic_gcd_bound_of_not_quarter_density
import Theorems.Thm_ErdosProblems_Erdos243_dvdChain_eventuallyConstant_of_cofinally_bounded
import Theorems.Thm_ErdosProblems_Erdos243_tailGcd_dvd_succ
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
    (q A B : ℤ) (hA : A ≠ 0) (hpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hclear : ∀ k : ℕ, (q : ℚ) * P k =
      (A : ℚ) * (k : ℚ) * ((k : ℚ) + 1) * ((k : ℚ) + 2) + (B : ℚ))
    (hlow : ¬ LowerDensityAtLeast {n : ℕ | (C n : ℚ) ≠ P n} (1 / 4)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Nat.gcd (C n) (D n) = Nat.gcd (C N) (D N) := by
  apply dvdChain_eventuallyConstant_of_cofinally_bounded
    (fun n ↦ Nat.gcd (C n) (D n)) (6 * A).natAbs
    (fun n ↦ Nat.gcd_pos_of_pos_left _ (hpos n))
    (fun n ↦ tailGcd_dvd_succ _ _ _ _ _ (hC n) (hD n))
  intro n
  exact ⟨n, le_rfl, cubic_gcd_bound_of_not_quarter_density a C D P q A B hA hC hD
    hclear hlow n⟩
