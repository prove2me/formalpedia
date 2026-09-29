-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.integral_cubic_mod_five_density
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:00:20.738399+00:00
-- url     : https://prove2.me/submissions/797bef00-5c3b-4776-b360-004e2eed29a2

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_integral_cubic_single_prime_density
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
# Single-prime cubic obstructions without the window-length loss

A fixed prime p >= 3 supplies disjoint three-windows with
lower exceptional density 1/p, rather than 1/(3*p). A concrete modulo-five
corollary constructs the prime, root, and nonsquare witness. This corollary
is unconditional; it does not postulate a good-prime family.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11
/-- The finite nonsquare certificate is checked by kernel reduction when run,
not by native evaluation and not by an external Python residue table. -/
theorem three_not_isSquare_zmod_five : ¬ IsSquare (3 : ZMod 5) := by
  decide
end ErdosProblems.Erdos243.PaperCompleteR11

open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution
    (a u v : ℕ → ℤ) (m c : ℤ) (T : ℕ)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (hm : (m : ZMod 5) ≠ 0)
    (hc : (c : ZMod 5) = (m : ZMod 5) ∨ (c : ZMod 5) = -(m : ZMod 5)) :
    LowerDensityAtLeast {n : ℕ | u n ≠ m * risingBinomial n + c} (1 / 5) := by
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  rcases hc with hc | hc
  · apply integral_cubic_single_prime_density a u v m c T 5 (by decide)
      hnum hden (3 : ZMod 5)
    · calc
        (m : ZMod 5) * ((3 : ZMod 5) ^ 3 - 3) + ((6 * c : ℤ) : ZMod 5) =
            (m : ZMod 5) * ((3 : ZMod 5) ^ 3 - 3) + 6 * (m : ZMod 5) := by
              push_cast
              rw [hc]
        _ = (30 : ZMod 5) * (m : ZMod 5) := by ring
        _ = 0 := by
          have h30 : (30 : ZMod 5) = 0 := by decide
          rw [h30, zero_mul]
    · exact mul_ne_zero (mul_ne_zero (by decide) hm) (by decide)
    · convert three_not_isSquare_zmod_five using 1 <;> decide
  · apply integral_cubic_single_prime_density a u v m c T 5 (by decide)
      hnum hden (2 : ZMod 5)
    · push_cast
      rw [hc]
      norm_num <;> ring_nf <;> norm_num
    · exact mul_ne_zero (mul_ne_zero (by decide) hm) (by decide)
    · convert three_not_isSquare_zmod_five using 1 <;> decide
