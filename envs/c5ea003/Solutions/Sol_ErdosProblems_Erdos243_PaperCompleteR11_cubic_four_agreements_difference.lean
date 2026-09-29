-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.cubic_four_agreements_difference
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:21:34.237595+00:00
-- url     : https://prove2.me/submissions/b4c048ba-04a4-42a2-a9ea-9ecd3095f10b

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
theorem solution (C : ℕ → ℕ) (P : ℕ → ℚ)
    (q A B : ℤ) (n : ℕ)
    (hclear : ∀ k : ℕ, (q : ℚ) * P k =
      (A : ℚ) * (k : ℚ) * ((k : ℚ) + 1) * ((k : ℚ) + 2) + (B : ℚ))
    (hagree : ∀ j : ℕ, j < 4 → (C (n + j) : ℚ) = P (n + j)) :
    q * ((C (n + 3) : ℤ) - 3 * (C (n + 2) : ℤ) +
      3 * (C (n + 1) : ℤ) - (C n : ℤ)) = 6 * A := by
  have h0 := hclear n
  have h1 := hclear (n + 1)
  have h2 := hclear (n + 2)
  have h3 := hclear (n + 3)
  have ha0 : (C n : ℚ) = P n := by simpa using hagree 0 (by decide)
  rw [← ha0] at h0
  rw [← hagree 1 (by decide)] at h1
  rw [← hagree 2 (by decide)] at h2
  rw [← hagree 3 (by decide)] at h3
  have hQ : (q : ℚ) * ((C (n + 3) : ℚ) - 3 * (C (n + 2) : ℚ) +
      3 * (C (n + 1) : ℚ) - (C n : ℚ)) = 6 * (A : ℚ) := by
    push_cast at h1 h2 h3
    linear_combination h3 - 3 * h2 + 3 * h1 - h0
  exact_mod_cast hQ
