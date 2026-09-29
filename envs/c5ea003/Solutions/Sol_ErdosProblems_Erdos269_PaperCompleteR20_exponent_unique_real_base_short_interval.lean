-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperCompleteR20.exponent_unique_real_base_short_interval
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:22:43.130825+00:00
-- url     : https://prove2.me/submissions/53cbed9f-73f8-4274-9f6a-741a2e3de3a9

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace ErdosProblems.Erdos269.PaperCompleteR20
end ErdosProblems.Erdos269.PaperCompleteR20

/-! Uniqueness in a real short multiplicative interval, including real bases. -/

open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperCompleteR20 in
theorem solution
    {base lo hi weight : ℝ} {a b : ℕ}
    (hbase : 1 ≤ base) (hweight : 0 ≤ weight)
    (hwidth : hi ≤ base * lo)
    (haLo : lo ≤ base ^ a * weight) (haHi : base ^ a * weight < hi)
    (hbLo : lo ≤ base ^ b * weight) (hbHi : base ^ b * weight < hi) :
    a = b := by
  have hbase0 : 0 ≤ base := le_trans (by norm_num) hbase
  have impossible : ∀ i j : ℕ, i < j → lo ≤ base ^ i * weight →
      base ^ j * weight < hi → False := by
    intro i j hij hiLo hjHi
    have hpow : base ^ (i + 1) ≤ base ^ j := pow_le_pow_right₀ hbase (by omega)
    have hcontra : hi < hi := calc
      hi ≤ base * lo := hwidth
      _ ≤ base * (base ^ i * weight) := mul_le_mul_of_nonneg_left hiLo hbase0
      _ = base ^ (i + 1) * weight := by rw [pow_succ]; ring
      _ ≤ base ^ j * weight := mul_le_mul_of_nonneg_right hpow hweight
      _ < hi := hjHi
    exact lt_irrefl hi hcontra
  rcases lt_trichotomy a b with hab | hab | hab
  · exact (impossible a b hab haLo hbHi).elim
  · exact hab
  · exact (impossible b a hab hbLo haHi).elim
