-- Prove2me | solution 1 for flt5_pow5_sum_natAbs_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-12T15:56:29.8843+00:00
-- url     : https://prove2.me/submissions/5ce4758b-5e8f-44f2-8300-46494ef080d8

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

-- theorem flt5_pow5_sum_natAbs_bound:
-- p^5+q^5=c1^5, p≠0, q≠0, 0<p*q → p.natAbs≤c1.natAbs ∧ q.natAbs≤c1.natAbs
-- 0<p*q means p,q same sign. Case p>0,q>0: p^5 < c1^5 (strict mono) → p < c1 → |p| ≤ |c1|.
-- Case p<0,q<0: reduce to (-p,-q,-c1).

theorem solution (p q c1 : ℤ) (h : p ^ 5 + q ^ 5 = c1 ^ 5)
    (hp : p ≠ 0) (hq : q ≠ 0) (hpq : 0 < p * q) :
    p.natAbs ≤ c1.natAbs ∧ q.natAbs ≤ c1.natAbs := by
  -- x^5 is strictly monotone on ℤ (odd exponent)
  have mono5 : StrictMono (fun x : ℤ => x ^ 5) :=
    Odd.strictMono_pow (show Odd 5 from ⟨2, by norm_num⟩)
  -- Helper: if 0 < a < b (ℤ), then a.natAbs < b.natAbs
  have natAbs_lt : ∀ a b : ℤ, 0 < a → a < b → a.natAbs < b.natAbs := by
    intros a b ha hab
    have hb : 0 < b := lt_trans ha hab
    have ha' : (a.natAbs : ℤ) = a := Int.natAbs_of_nonneg (le_of_lt ha)
    have hb' : (b.natAbs : ℤ) = b := Int.natAbs_of_nonneg (le_of_lt hb)
    have h_int : (a.natAbs : ℤ) < (b.natAbs : ℤ) := by rw [ha', hb']; exact hab
    exact_mod_cast h_int
  -- Case split: p and q have the same sign
  rcases mul_pos_iff.mp hpq with ⟨hp_pos, hq_pos⟩ | ⟨hp_neg, hq_neg⟩
  · -- Case 1: p > 0, q > 0
    have hc1_pos : 0 < c1 := by
      apply mono5.lt_iff_lt.mp
      simp only [zero_pow (show 5 ≠ 0 by norm_num)]
      linarith [pow_pos hp_pos 5, pow_pos hq_pos 5, h.symm]
    have hp_lt : p < c1 := mono5.lt_iff_lt.mp
      (show p ^ 5 < c1 ^ 5 by linarith [pow_pos hq_pos 5, h.symm])
    have hq_lt : q < c1 := mono5.lt_iff_lt.mp
      (show q ^ 5 < c1 ^ 5 by linarith [pow_pos hp_pos 5, h.symm])
    exact ⟨Nat.le_of_lt (natAbs_lt p c1 hp_pos hp_lt),
           Nat.le_of_lt (natAbs_lt q c1 hq_pos hq_lt)⟩
  · -- Case 2: p < 0, q < 0; apply Case 1 to (-p, -q, -c1)
    have hnp : 0 < -p := by linarith
    have hnq : 0 < -q := by linarith
    have h' : (-p) ^ 5 + (-q) ^ 5 = (-c1) ^ 5 := by linear_combination -h
    have hnc1_pos : 0 < -c1 := by
      apply mono5.lt_iff_lt.mp
      simp only [zero_pow (show 5 ≠ 0 by norm_num)]
      linarith [pow_pos hnp 5, pow_pos hnq 5, h'.symm]
    have hp_lt : -p < -c1 := mono5.lt_iff_lt.mp
      (show (-p) ^ 5 < (-c1) ^ 5 by linarith [pow_pos hnq 5, h'.symm])
    have hq_lt : -q < -c1 := mono5.lt_iff_lt.mp
      (show (-q) ^ 5 < (-c1) ^ 5 by linarith [pow_pos hnp 5, h'.symm])
    -- p.natAbs = (-p).natAbs and c1.natAbs = (-c1).natAbs
    constructor
    · have h1 := Nat.le_of_lt (natAbs_lt (-p) (-c1) hnp hp_lt)
      rwa [Int.natAbs_neg, Int.natAbs_neg] at h1
    · have h2 := Nat.le_of_lt (natAbs_lt (-q) (-c1) hnq hq_lt)
      rwa [Int.natAbs_neg, Int.natAbs_neg] at h2

