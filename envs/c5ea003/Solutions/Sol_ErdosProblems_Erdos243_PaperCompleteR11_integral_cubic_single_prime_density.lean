-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.integral_cubic_single_prime_density
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:54:29.778839+00:00
-- url     : https://prove2.me/submissions/29268a91-efd6-47df-9a40-d79d2b988b7e

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_six_mul_risingBinomial
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_disjoint_periodic_lowerDensity
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_rational_cubic_residue_window_hit
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
/-- Exact clearing of the integer-valued binomial profile over the rationals. -/
theorem integral_binomial_profile_clearing (m c : ℤ) (n : ℕ) :
    (6 : ℚ) * (((m * risingBinomial n + c : ℤ)) : ℚ) =
      (m : ℚ) * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + ((6 * c : ℤ) : ℚ) := by
  have hB : (6 : ℚ) * (risingBinomial n : ℚ) =
      (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) := by
    exact_mod_cast six_mul_risingBinomial n
  push_cast
  linear_combination (m : ℚ) * hB
end ErdosProblems.Erdos243.PaperCompleteR11

open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution
    (a u v : ℕ → ℤ) (m c : ℤ) (T p : ℕ) [Fact p.Prime] (hp : 3 ≤ p)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (r : ZMod p)
    (hroot : (m : ZMod p) * (r ^ 3 - r) + ((6 * c : ℤ) : ZMod p) = 0)
    (hfactor : 3 * (m : ZMod p) * r ≠ 0) (hns : ¬ IsSquare (r ^ 2 - 1)) :
    LowerDensityAtLeast {n : ℕ | u n ≠ m * risingBinomial n + c} (1 / (p : ℝ)) := by
  letI : NeZero p := ⟨by omega⟩
  letI : NeZero p := ⟨by omega⟩
  let start := (r - 2).val + p * T
  apply disjoint_periodic_lowerDensity _ start p 3 (by omega) hp
  intro k
  have hT : T ≤ start + p * k := by
    have hmul := Nat.mul_le_mul_right T (show 1 ≤ p by omega)
    dsimp [start]
    omega
  have hphase : ((start + p * k : ℕ) : ZMod p) = r - 2 := by
    simp [start, ZMod.natCast_zmod_val]
  obtain ⟨j, hj, hne⟩ := rational_cubic_residue_window_hit a u v
    (fun n ↦ ((m * risingBinomial n + c : ℤ) : ℚ)) 6 m (6 * c)
    T (start + p * k) hT (integral_binomial_profile_clearing m c)
    hnum hden p r hroot hfactor hns hphase
  refine ⟨j, hj, ?_⟩
  intro heq
  exact hne (congrArg (fun z : ℤ ↦ (z : ℚ)) heq)
