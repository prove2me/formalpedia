-- Prove2me | solution 1 for lean_workbook_plus_81452
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T01:45:21.122292+00:00
-- url     : https://prove2.me/submissions/72eb3b64-2cc2-4153-88ed-3bc04d93c648

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

private lemma adjacent_choose_two (m : ℕ) :
    (m + 1).choose 2 + m.choose 2 = m ^ 2 := by
  induction m with
  | zero => decide
  | succ m ih =>
    have h1 := Nat.choose_succ_succ' (m + 1) 1
    have h2 := Nat.choose_succ_succ' m 1
    simp only [Nat.choose_one_right] at h1 h2
    nlinarith

theorem solution (n : ℕ) : (n + 1).choose 3 - (n - 1).choose 3 = (n - 1) ^ 2 := by
  cases n with
  | zero => decide
  | succ m =>
    have h1 : (m + 2).choose 3 = (m + 1).choose 2 + (m + 1).choose 3 := by
      simpa [Nat.add_assoc] using Nat.choose_succ_succ' (m + 1) 2
    have h2 : (m + 1).choose 3 = m.choose 2 + m.choose 3 := Nat.choose_succ_succ' m 2
    have hp := adjacent_choose_two m
    simpa using (show (m + 2).choose 3 - m.choose 3 = m ^ 2 by omega)

#print axioms solution
