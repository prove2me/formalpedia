-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR7.clearedIntegerNumerator_cast
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:11:15.777229+00:00
-- url     : https://prove2.me/submissions/a8c1f0e5-4b74-44d7-ac17-7171d845b67f

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_RealTail
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_CanonicalState
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













/-- Each denominator in the prefix divides the prefix product, and the
natural quotient casts to the corresponding real quotient. -/
theorem prefix_quotient_cast (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (n j : ℕ) (hj : j ∈ Finset.range n) :
    ((prefixProduct a n / a j : ℕ) : ℝ) =
      (prefixProduct a n : ℝ) / (a j : ℝ) := by
  have hd : a j ∣ prefixProduct a n := Finset.dvd_prod_of_mem a hj
  have heq : (a j : ℝ) * ((prefixProduct a n / a j : ℕ) : ℝ) =
      (prefixProduct a n : ℝ) := by
    exact_mod_cast Nat.mul_div_cancel' hd
  have hne : (a j : ℝ) ≠ 0 := by exact_mod_cast (ha j).ne'
  apply (eq_div_iff hne).mpr
  simpa only [mul_comm] using heq
end ErdosProblems.Erdos243.PaperCompleteR7

open Filter
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR7 in
theorem solution
    (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q) (n : ℕ) :
    (clearedIntegerNumerator a p q n : ℝ) =
      (canonicalDenominator a q n : ℝ) *
        ((p : ℝ) / (q : ℝ) - ∑ j ∈ Finset.range n, 1 / (a j : ℝ)) := by
  have hsum : (∑ j ∈ Finset.range n,
      (q : ℝ) * ((prefixProduct a n / a j : ℕ) : ℝ)) =
      (q : ℝ) * (prefixProduct a n : ℝ) *
        (∑ j ∈ Finset.range n, 1 / (a j : ℝ)) := by
    calc
      (∑ j ∈ Finset.range n,
          (q : ℝ) * ((prefixProduct a n / a j : ℕ) : ℝ)) =
          ∑ j ∈ Finset.range n,
            ((q : ℝ) * (prefixProduct a n : ℝ)) * (1 / (a j : ℝ)) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [prefix_quotient_cast a ha n j hj]
              ring
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hqne : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hterm : ∀ j : ℕ,
      (((prefixProduct a n : ℤ) / (a j : ℤ) : ℤ) : ℝ) =
        ((prefixProduct a n / a j : ℕ) : ℝ) := by
    intro j
    norm_cast
  unfold clearedIntegerNumerator canonicalDenominator
  push_cast
  simp only [hterm]
  rw [hsum]
  field_simp [hqne]
  <;> ring
