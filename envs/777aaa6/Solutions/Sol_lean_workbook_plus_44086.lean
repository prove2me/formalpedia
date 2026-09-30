-- Prove2me | solution 1 for lean_workbook_plus_44086
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:42:21.422626+00:00
-- url     : https://prove2.me/submissions/af8249ef-32d7-43f6-86e1-a27de1bee04e

import Mathlib.Analysis.Complex.Basic
theorem solution : 2 ^ 2009 ≡ 2 [MOD 10] := by
  have h : ∀ k : ℕ, 2 ^ (4 * k + 1) % 10 = 2 := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      have e : 2 ^ (4 * (k + 1) + 1) = 2 ^ (4 * k + 1) * 16 := by ring
      rw [e, Nat.mul_mod, ih]
  have e : (2009 : ℕ) = 4 * 502 + 1 := by norm_num
  show 2 ^ 2009 % 10 = 2 % 10
  rw [e]
  exact h 502
