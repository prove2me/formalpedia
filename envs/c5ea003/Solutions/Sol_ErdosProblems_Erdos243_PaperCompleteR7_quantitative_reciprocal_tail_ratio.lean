-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR7.quantitative_reciprocal_tail_ratio
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:21:42.927014+00:00
-- url     : https://prove2.me/submissions/58d56b1d-cd75-4494-8204-23e8f021fd12

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_RealTail
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_CanonicalState
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR7_reciprocal_successive_ratio_tendsto_zero
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR7_realTail_step
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR7_realTail_leading_term
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR7_realTail_pos
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR7_realTail_geometric_bound
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
    (hs : Summable (fun n ↦ 1 / (a n : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1)) :
    ∃ N, ∀ n, N ≤ n →
      |(a n : ℝ) * realTail (fun k ↦ 1 / (a k : ℝ)) (n + 1) /
          realTail (fun k ↦ 1 / (a k : ℝ)) n -
        (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)| ≤ 16 / (a n : ℝ) := by
  let t : ℕ → ℝ := fun n ↦ 1 / (a n : ℝ)
  let b : ℕ → ℝ := fun n ↦ (a n : ℝ) * realTail t n
  have hap : ∀ n, (0 : ℝ) < (a n : ℝ) := fun n ↦ by exact_mod_cast hpos n
  have htp : ∀ n, 0 < t n := fun n ↦ one_div_pos.mpr (hap n)
  have hq : Tendsto (fun n ↦ (a n : ℝ) ^ 2 / (a (n + 1) : ℝ))
      atTop (nhds 1) := by
    simpa only [inv_div, inv_one] using hgrowth.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  obtain ⟨Nq, hNq⟩ := Metric.tendsto_atTop.mp hq 1 (by norm_num)
  have hqb : ∀ n, Nq ≤ n → (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) ≤ 2 := by
    intro n hn
    have hh := hNq n hn
    rw [Real.dist_eq] at hh
    have := (abs_lt.mp hh).2
    linarith
  have hr := reciprocal_successive_ratio_tendsto_zero a ha hpos hgrowth
  obtain ⟨Nr, hNr⟩ := Metric.tendsto_atTop.mp hr (1 / 2) (by norm_num)
  have hstep : ∀ n, Nr ≤ n → t (n + 1) ≤ (1 / 2) * t n := by
    intro n hn
    have hp : 0 ≤ t (n + 1) / t n := div_nonneg (htp _).le (htp _).le
    have hlt : t (n + 1) / t n < 1 / 2 := by
      have h := hNr n hn
      rw [Real.dist_eq, sub_zero,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤
          1 / (a (n + 1) : ℝ) / (1 / (a n : ℝ)))] at h
      exact h
    exact (div_le_iff₀ (htp n)).mp hlt.le
  have htail : ∀ n, Nr ≤ n → realTail t n ≤ 2 / (a n : ℝ) := by
    intro n hn
    have hh := realTail_geometric_bound t hs (fun j ↦ (htp j).le)
      (1 / 2) (by norm_num) (by norm_num) Nr n hn hstep
    rw [show (1 - (1 / 2 : ℝ))⁻¹ = 2 by norm_num] at hh
    calc realTail t n ≤ 2 * t n := hh
      _ = 2 / (a n : ℝ) := by dsimp only [t]; ring
  have hb1 : ∀ n, 1 ≤ b n := by
    intro n
    have hlead := realTail_leading_term t hs (fun j ↦ (htp j).le) n
    have hh := mul_le_mul_of_nonneg_left hlead (hap n).le
    have hcancel : (a n : ℝ) * t n = 1 := by
      dsimp [t]
      field_simp [(hap n).ne']
    simpa only [hcancel] using hh
  let N := max Nq Nr
  have hberr : ∀ n, N ≤ n → b n - 1 ≤ 4 / (a n : ℝ) := by
    intro n hn
    have hid : b n - 1 = (a n : ℝ) * realTail t (n + 1) := by
      dsimp [b]
      rw [realTail_step t hs n]
      dsimp [t]
      field_simp [(hap n).ne']
      <;> ring
    rw [hid]
    have ht := htail (n + 1) (by dsimp [N] at hn; omega)
    calc
      (a n : ℝ) * realTail t (n + 1) ≤ (a n : ℝ) * (2 / (a (n + 1) : ℝ)) :=
        mul_le_mul_of_nonneg_left ht (hap n).le
      _ = (2 * ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ))) / (a n : ℝ) := by
        field_simp [(hap n).ne', (hap (n + 1)).ne']
        <;> ring
      _ ≤ 4 / (a n : ℝ) := by
        apply (div_le_div_iff₀ (hap n) (hap n)).mpr
        have hh := hqb n (by dsimp [N] at hn; omega)
        nlinarith [mul_nonneg (hap n).le (show 0 ≤ 2 -
          (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) by linarith)]
  refine ⟨N, fun n hn ↦ ?_⟩
  have hbpos : 0 < b n := lt_of_lt_of_le (by norm_num) (hb1 n)
  have hqnonneg : 0 ≤ (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) :=
    div_nonneg (sq_nonneg _) (hap _).le
  have hqdiv : (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) / b n ≤ 2 := by
    apply (div_le_iff₀ hbpos).mpr
    have hqq := hqb n (by dsimp [N] at hn; omega)
    have hb := hb1 n
    nlinarith
  have hnexterr : b (n + 1) - 1 ≤ 4 / (a n : ℝ) := by
    have hh := hberr (n + 1) (by omega)
    apply hh.trans
    apply (div_le_div_iff₀ (hap (n + 1)) (hap n)).mpr
    have hmono : (a n : ℝ) ≤ (a (n + 1) : ℝ) := by
      exact_mod_cast (ha (Nat.lt_succ_self n)).le
    linarith
  have hdiff : |b (n + 1) - b n| ≤ 8 / (a n : ℝ) := by
    have h0 := hb1 n
    have h1 := hb1 (n + 1)
    have he := hberr n hn
    have hnz : 0 ≤ 4 / (a n : ℝ) := div_nonneg (by norm_num) (hap n).le
    have hrel : (8 : ℝ) / (a n : ℝ) = 2 * (4 / (a n : ℝ)) := by ring
    rw [abs_le]
    constructor <;> linarith
  have hid : (a n : ℝ) * realTail t (n + 1) / realTail t n -
        (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) =
      ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) / b n) * (b (n + 1) - b n) := by
    have hx : realTail t n ≠ 0 := (realTail_pos t hs htp n).ne'
    dsimp [b]
    field_simp [(hap n).ne', (hap (n + 1)).ne', hx]
    <;> ring
  rw [hid, abs_mul, abs_of_nonneg (div_nonneg hqnonneg hbpos.le)]
  calc
    ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) / b n) * |b (n + 1) - b n|
        ≤ 2 * (8 / (a n : ℝ)) :=
      mul_le_mul hqdiv hdiff (abs_nonneg _) (by norm_num)
    _ = 16 / (a n : ℝ) := by ring
