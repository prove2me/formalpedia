-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR7.canonical_integer_tail
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:21:41.04574+00:00
-- url     : https://prove2.me/submissions/edeb53e6-6baa-44be-af2b-a8975cf54368

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_RealTail
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_CanonicalState
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR7_clearedIntegerNumerator_cast
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR7_realTail_step
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR7_realTail_pos
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Constructing the canonical integer state and its analytic hypotheses

Compiled candidates.  The rational sum is supplied by its explicit
integer numerator p and positive natural denominator q; it is NOT replaced
by an assumed integer-tail representation.

The cleared numerator is an explicit integer finite sum.  Its positivity
is derived from the positive real tail.  All casting, exact natural
recurrences, and normalised-vanishing inputs are then concluded.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR7
open Filter
open scoped BigOperators









theorem prefixProduct_pos (a : ℕ → ℕ) (ha : ∀ n, 0 < a n) (n : ℕ) :
    0 < prefixProduct a n := by
  exact Finset.prod_pos (fun j _ ↦ ha j)

theorem prefixProduct_succ (a : ℕ → ℕ) (n : ℕ) :
    prefixProduct a (n + 1) = prefixProduct a n * a n := by
  exact Finset.prod_range_succ a n





/-- The real tail is the prescribed rational sum minus its exact prefix. -/
theorem realTail_eq_rational_sub_prefix
    (a : ℕ → ℕ) (p : ℤ) (q : ℕ)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ))) (n : ℕ) :
    realTail (fun k ↦ 1 / (a k : ℝ)) n =
      (p : ℝ) / (q : ℝ) - ∑ j ∈ Finset.range n, 1 / (a j : ℝ) := by
  have hsplit := hs.summable.sum_add_tsum_nat_add n
  rw [hs.tsum_eq] at hsplit
  change (∑ j ∈ Finset.range n, 1 / (a j : ℝ)) +
    realTail (fun k ↦ 1 / (a k : ℝ)) n = (p : ℝ) / (q : ℝ) at hsplit
  linarith
end ErdosProblems.Erdos243.PaperCompleteR7

open Filter
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR7 in
theorem solution
    (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ))) :
    let C := canonicalNaturalNumerator a p q
    let D := canonicalDenominator a q
    (∀ n, 0 < C n) ∧ (∀ n, 0 < D n) ∧
    (∀ n, C (n + 1) + D n = a n * C n) ∧
    (∀ n, D (n + 1) = a n * D n) ∧
    (∀ n, (C n : ℝ) = (D n : ℝ) * realTail (fun k ↦ 1 / (a k : ℝ)) n) := by
  let C := canonicalNaturalNumerator a p q
  let D := canonicalDenominator a q
  have hdpos : ∀ n, 0 < D n := by
    intro n
    exact Nat.mul_pos hq (prefixProduct_pos a ha n)
  have hreprInt : ∀ n, (clearedIntegerNumerator a p q n : ℝ) =
      (D n : ℝ) * realTail (fun k ↦ 1 / (a k : ℝ)) n := by
    intro n
    rw [clearedIntegerNumerator_cast a ha p q hq n,
      realTail_eq_rational_sub_prefix a p q hs n]
  have hcintpos : ∀ n, 0 < clearedIntegerNumerator a p q n := by
    intro n
    have hreal : (0 : ℝ) < (clearedIntegerNumerator a p q n : ℝ) := by
      rw [hreprInt n]
      apply mul_pos (by exact_mod_cast hdpos n)
      exact realTail_pos _ hs.summable
        (fun k ↦ one_div_pos.mpr (by exact_mod_cast ha k)) n
    exact_mod_cast hreal
  have hcast : ∀ n, (C n : ℤ) = clearedIntegerNumerator a p q n := by
    intro n
    exact Int.toNat_of_nonneg (hcintpos n).le
  have hcpos : ∀ n, 0 < C n := by
    intro n
    have hcc := hcast n
    have hp := hcintpos n
    omega
  have hrep : ∀ n, (C n : ℝ) =
      (D n : ℝ) * realTail (fun k ↦ 1 / (a k : ℝ)) n := by
    intro n
    have hcc : (C n : ℝ) = (clearedIntegerNumerator a p q n : ℝ) := by
      exact_mod_cast hcast n
    exact hcc.trans (hreprInt n)
  have hd : ∀ n, D (n + 1) = a n * D n := by
    intro n
    change q * prefixProduct a (n + 1) = a n * (q * prefixProduct a n)
    rw [prefixProduct_succ]
    ring
  have hc : ∀ n, C (n + 1) + D n = a n * C n := by
    intro n
    have hane : (a n : ℝ) ≠ 0 := by exact_mod_cast (ha n).ne'
    have hreal : (C (n + 1) : ℝ) + (D n : ℝ) = (a n : ℝ) * (C n : ℝ) := by
      rw [hrep (n + 1), hrep n, hd n, Nat.cast_mul,
        realTail_step _ hs.summable n]
      field_simp [hane]
      <;> ring
    exact_mod_cast hreal
  exact ⟨hcpos, hdpos, hc, hd, hrep⟩
