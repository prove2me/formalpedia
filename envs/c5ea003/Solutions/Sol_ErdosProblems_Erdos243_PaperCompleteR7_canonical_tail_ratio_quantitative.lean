-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR7.canonical_tail_ratio_quantitative
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:26:21.391869+00:00
-- url     : https://prove2.me/submissions/77a38d0a-483f-4236-ac4e-cc5927cac993

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_RealTail
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_CanonicalState
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR7_realTail_pos
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR7_canonical_integer_tail
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR7_quadratic_growth_exponential_lower_bound
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR7_quantitative_reciprocal_tail_ratio
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
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1)) :
    let C := canonicalNaturalNumerator a p q
    (∃ N, ∀ n, N ≤ n →
      |(C (n + 1) : ℝ) / (C n : ℝ) -
        (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)| ≤ 16 / (a n : ℝ)) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ N, ∀ n, N ≤ n →
      Real.exp (c * (2 : ℝ) ^ n) ≤ (a n : ℝ)) := by
  let C := canonicalNaturalNumerator a p q
  let D := canonicalDenominator a q
  obtain ⟨hcpos, hdpos, hc, hd, hrep⟩ := canonical_integer_tail a hpos p q hq hs
  refine ⟨?_, quadratic_growth_exponential_lower_bound a ha hpos hgrowth⟩
  obtain ⟨N, hN⟩ := quantitative_reciprocal_tail_ratio a ha hpos hs.summable hgrowth
  refine ⟨N, fun n hn ↦ ?_⟩
  have heq : (C (n + 1) : ℝ) / (C n : ℝ) =
      (a n : ℝ) * realTail (fun k ↦ 1 / (a k : ℝ)) (n + 1) /
        realTail (fun k ↦ 1 / (a k : ℝ)) n := by
    rw [hrep (n + 1), hrep n, hd n, Nat.cast_mul]
    have hdne : ((canonicalDenominator a q n : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (hdpos n).ne'
    have hx : realTail (fun k ↦ 1 / (a k : ℝ)) n ≠ 0 :=
      (realTail_pos _ hs.summable (fun k ↦ one_div_pos.mpr
        (by exact_mod_cast hpos k)) n).ne'
    field_simp [hdne, hx]
    <;> ring
  rw [heq]
  exact hN n hn
