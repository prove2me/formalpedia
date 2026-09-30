-- Prove2me | solution 1 for lean_workbook_plus_66907
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:56:06.978466+00:00
-- url     : https://prove2.me/submissions/789e80b8-01cc-429f-9693-a4c807e8818e

import Mathlib.Tactic.Linarith

theorem solution : ∀ n : ℕ, 6 ∣ n * (n + 1) * (2 * n + 1) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      obtain ⟨q, hq⟩ := ih
      refine ⟨q + (n + 1) ^ 2, ?_⟩
      nlinarith [hq]
