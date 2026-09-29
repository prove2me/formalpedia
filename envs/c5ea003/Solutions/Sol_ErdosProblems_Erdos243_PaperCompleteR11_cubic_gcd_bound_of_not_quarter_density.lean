-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.cubic_gcd_bound_of_not_quarter_density
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:41:26.056167+00:00
-- url     : https://prove2.me/submissions/c8991226-d526-4fad-b0c3-fec92c757502

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubic_gcd_dvd_of_not_quarter_density
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
    (q A B : ℤ) (hA : A ≠ 0)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hclear : ∀ k : ℕ, (q : ℚ) * P k =
      (A : ℚ) * (k : ℚ) * ((k : ℚ) + 1) * ((k : ℚ) + 2) + (B : ℚ))
    (hlow : ¬ LowerDensityAtLeast {n : ℕ | (C n : ℚ) ≠ P n} (1 / 4)) :
    ∀ s : ℕ, Nat.gcd (C s) (D s) ≤ (6 * A).natAbs := by
  intro s
  obtain ⟨k, hk⟩ := cubic_gcd_dvd_of_not_quarter_density a C D P q A B hC hD hclear hlow s
  have hd : Nat.gcd (C s) (D s) ∣ (6 * A).natAbs := by
    refine ⟨k.natAbs, ?_⟩
    rw [hk, Int.natAbs_mul, Int.natAbs_natCast]
  have hpos : 0 < (6 * A).natAbs := Int.natAbs_pos.mpr (mul_ne_zero (by norm_num) hA)
  exact Nat.le_of_dvd hpos hd
