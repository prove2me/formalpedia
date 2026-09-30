-- Prove2me | solution 1 for lean_workbook_plus_10181
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:21:29.034857+00:00
-- url     : https://prove2.me/submissions/bd990604-a504-4557-a0c3-12428d4eecd7

import Mathlib.Analysis.Complex.Basic

theorem solution (P : ℕ → Prop) (base : P 0) (induction : ∀ m : ℕ, P m → P (m + 1)) : ∀ n : ℕ, P n := by
  intro n
  induction n with
  | zero => exact base
  | succ k ih => exact ‹∀ m : ℕ, P m → P (m + 1)› k ih
