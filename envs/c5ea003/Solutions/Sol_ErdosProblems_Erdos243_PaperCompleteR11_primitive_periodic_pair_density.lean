-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.primitive_periodic_pair_density
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T00:19:41.830609+00:00
-- url     : https://prove2.me/submissions/1a67e446-ee50-4cc4-b0d8-d942fa11b6b8

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_disjoint_periodic_lowerDensity
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_primitive_pair_profile_hit
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
theorem solution (u : ℕ → ℕ) (P : ℕ → ℤ)
    (T d s : ℕ) (hd : 2 ≤ d) (hs : 2 ≤ s)
    (hcop : ∀ n, T ≤ n → Nat.Coprime (u n) (u (n + 1)))
    (hdiv : ∀ n k : ℕ, n + 1 = s * k →
      (d : ℤ) ∣ P n ∧ (d : ℤ) ∣ P (n + 1)) :
    LowerDensityAtLeast {n : ℕ | (u n : ℤ) ≠ P n} (1 / (s : ℝ)) := by
  let r := s * T + (s - 1)
  apply disjoint_periodic_lowerDensity _ r s 2 (by omega) hs
  intro k
  let n := r + s * k
  have hs1 : s - 1 + 1 = s := by omega
  have hphase : n + 1 = s * (T + k + 1) := by
    dsimp [n, r]
    nlinarith
  have hnT : T ≤ n := by
    have hh := Nat.mul_le_mul_right T (show 1 ≤ s by omega)
    dsimp [n, r]
    nlinarith
  obtain ⟨h0, h1⟩ := hdiv n (T + k + 1) hphase
  exact primitive_pair_profile_hit u P n d hd (hcop n hnT) h0 h1
