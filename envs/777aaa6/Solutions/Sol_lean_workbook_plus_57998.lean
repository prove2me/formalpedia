-- Prove2me | solution 1 for lean_workbook_plus_57998
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:07:18.782861+00:00
-- url     : https://prove2.me/submissions/3fadaaa8-29b3-49a8-ad90-6dfec75343e8

import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic

private theorem least_multiple_above (N d : ℕ) (hd : 0 < d) :
    IsLeast {m : ℕ | N < m ∧ d ∣ m} (d * (N / d + 1)) := by
  refine ⟨⟨?_, ⟨N / d + 1, rfl⟩⟩, ?_⟩
  · have h := (Nat.div_lt_iff_lt_mul hd).mp (show N / d < N / d + 1 by omega)
    simpa only [Nat.mul_comm] using h
  · rintro m ⟨hm, k, rfl⟩
    have hk : N / d < k := (Nat.div_lt_iff_lt_mul hd).mpr (by
      simpa only [Nat.mul_comm] using hm)
    exact Nat.mul_le_mul_left d (by omega)

theorem solution : IsLeast {n : ℕ | 1000 < n ∧ 56 ∣ n} 1008 := by
  simpa only [Nat.reduceDiv, Nat.reduceAdd, Nat.reduceMul] using
    least_multiple_above 1000 56 (by decide)
