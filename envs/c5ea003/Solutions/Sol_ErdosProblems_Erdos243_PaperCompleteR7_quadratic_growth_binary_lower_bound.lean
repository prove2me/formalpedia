-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR7.quadratic_growth_binary_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:11:19.162834+00:00
-- url     : https://prove2.me/submissions/bccc3132-b787-43fa-b1f9-35422d6de0ed

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_RealTail
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_CanonicalState
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
# The quantitative canonical-tail lemma

Compiled candidates for the whole long-record `res:tailratio`.
The O(1/a_n) conclusion has an explicit eventual constant 16.  The growth
bound is first proved as an exact binary-power inequality, and then
converted to the exponential notation of the paper.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR7
open Filter
end ErdosProblems.Erdos243.PaperCompleteR7

open Filter
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR7 in
theorem solution
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1)) :
    ∃ N, ∀ k : ℕ, 2 * (2 : ℝ) ^ ((2 : ℕ) ^ k) ≤ (a (N + k) : ℝ) := by
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.mp hgrowth (1 / 2) (by norm_num)
  have hstep : ∀ n, N0 ≤ n → (a n : ℝ) ^ 2 ≤ 2 * (a (n + 1) : ℝ) := by
    intro n hn
    have hh := hN0 n hn
    rw [Real.dist_eq] at hh
    have hlo := (abs_lt.mp hh).1
    have hap : (0 : ℝ) < (a n : ℝ) := by exact_mod_cast hpos n
    have hratio : (1 / 2 : ℝ) ≤ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2 := by linarith
    have hmul := (le_div_iff₀ (pow_pos hap 2)).mp hratio
    linarith
  have hnat : ∀ n, n < a n := by
    intro n
    induction n with
    | zero => exact hpos 0
    | succ n ih =>
        have hh : a n < a (n + 1) := ha (Nat.lt_succ_self n)
        omega
  let N := max N0 3
  refine ⟨N, fun k ↦ ?_⟩
  induction k with
  | zero =>
      have h4 : 4 ≤ a N := by have hh := hnat N; dsimp [N] at *; omega
      norm_num only [pow_zero, pow_one, Nat.add_zero]
      exact_mod_cast h4
  | succ k ih =>
      have hg := hstep (N + k) (by dsimp [N]; omega)
      have hp : 0 ≤ 2 * (2 : ℝ) ^ ((2 : ℕ) ^ k) := by positivity
      have hsq := mul_self_le_mul_self hp ih
      have heq : (2 : ℝ) ^ ((2 : ℕ) ^ (k + 1)) =
          ((2 : ℝ) ^ ((2 : ℕ) ^ k)) ^ 2 := by
        rw [pow_succ, pow_mul]
      rw [heq]
      have hi : N + (k + 1) = N + k + 1 := by omega
      rw [hi]
      nlinarith
