-- Prove2me | solution 1 for lean_workbook_plus_40511
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:12:26.288188+00:00
-- url     : https://prove2.me/submissions/7746a984-c3fd-4c5e-9edb-9202e0d76bec

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace WeightedReciprocalBound

theorem gap_identity (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 ≤ t) :
    1 / (t + 1) * (1 / a + 1 / b) - (1 / (t * a + b) + 1 / (a + t * b)) =
      t * (a + b) * (a - b) ^ 2 /
        ((t + 1) * a * b * (t * a + b) * (a + t * b)) := by
  have ht1 : 0 < t + 1 := by positivity
  have hab : 0 < t * a + b := by positivity
  have hba : 0 < a + t * b := by positivity
  field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt ht1, ne_of_gt hab, ne_of_gt hba]
  <;> ring

theorem bound (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 ≤ t) :
    1 / (t * a + b) + 1 / (a + t * b) ≤ 1 / (t + 1) * (1 / a + 1 / b) := by
  apply sub_nonneg.mp
  rw [gap_identity a b t ha hb ht]
  positivity

theorem equality_iff (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (ht : 0 ≤ t) :
    1 / (t * a + b) + 1 / (a + t * b) = 1 / (t + 1) * (1 / a + 1 / b) ↔
      t = 0 ∨ a = b := by
  constructor
  · intro h
    have hden : (t + 1) * a * b * (t * a + b) * (a + t * b) ≠ 0 := by
      positivity
    have hzero : t * (a + b) * (a - b) ^ 2 /
        ((t + 1) * a * b * (t * a + b) * (a + t * b)) = 0 := by
      rw [← gap_identity a b t ha hb ht, h, sub_self]
    have hnum : t * (a + b) * (a - b) ^ 2 = 0 :=
      ((div_eq_zero_iff).mp hzero).resolve_right hden
    rcases mul_eq_zero.mp hnum with hprod | hsq
    · rcases mul_eq_zero.mp hprod with ht0 | hsum
      · exact Or.inl ht0
      · exact False.elim ((ne_of_gt (add_pos ha hb)) hsum)
    · exact Or.inr (sub_eq_zero.mp (eq_zero_of_pow_eq_zero hsq))
  · intro h
    have hnum : t * (a + b) * (a - b) ^ 2 = 0 := by
      rcases h with ht0 | hab
      · simp [ht0]
      · simp [hab]
    have hgap := gap_identity a b t ha hb ht
    rw [hnum, zero_div] at hgap
    exact (sub_eq_zero.mp hgap).symm

theorem nat_equality_iff (a b : ℝ) (n : ℕ) (ha : 0 < a) (hb : 0 < b) :
    1 / (n * a + b) + 1 / (a + n * b) = 1 / (n + 1) * (1 / a + 1 / b) ↔
      n = 0 ∨ a = b := by
  simpa using equality_iff a b (n : ℝ) ha hb (Nat.cast_nonneg n)

end WeightedReciprocalBound

theorem solution (a b : ℝ) (n : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (1 / (n * a + b) + 1 / (a + n * b)) ≤ (1 / (n + 1) * (1 / a + 1 / b)) := by
  exact WeightedReciprocalBound.bound a b (n : ℝ) ha hb (Nat.cast_nonneg n)
