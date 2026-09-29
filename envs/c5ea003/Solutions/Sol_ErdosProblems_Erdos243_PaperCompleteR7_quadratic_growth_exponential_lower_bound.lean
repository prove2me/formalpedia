-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR7.quadratic_growth_exponential_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:17:38.633499+00:00
-- url     : https://prove2.me/submissions/fe5a026b-d4cd-40c5-84f5-9ca51f7de5d8

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_RealTail
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_CanonicalState
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR7_quadratic_growth_binary_lower_bound
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
    ∃ c : ℝ, 0 < c ∧ ∃ N, ∀ n, N ≤ n →
      Real.exp (c * (2 : ℝ) ^ n) ≤ (a n : ℝ) := by
  obtain ⟨N, hN⟩ := quadratic_growth_binary_lower_bound a ha hpos hgrowth
  let c : ℝ := Real.log 2 / (2 : ℝ) ^ N
  have hc : 0 < c := div_pos (Real.log_pos (by norm_num)) (by positivity)
  refine ⟨c, hc, N, fun n hn ↦ ?_⟩
  let k := n - N
  have hnk : N + k = n := Nat.add_sub_of_le hn
  have hexp : Real.exp ((2 : ℝ) ^ k * Real.log 2) =
      (2 : ℝ) ^ ((2 : ℕ) ^ k) := by
    have hh := Real.exp_log (pow_pos (by norm_num : (0 : ℝ) < 2) ((2 : ℕ) ^ k))
    rw [Real.log_pow] at hh
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hh
  have hexponent : c * (2 : ℝ) ^ n = (2 : ℝ) ^ k * Real.log 2 := by
    rw [← hnk, pow_add]
    dsimp [c]
    field_simp
    <;> ring
  rw [hexponent, hexp]
  have hb := hN k
  rw [hnk] at hb
  have hp : 0 ≤ (2 : ℝ) ^ ((2 : ℕ) ^ k) := by positivity
  linarith
