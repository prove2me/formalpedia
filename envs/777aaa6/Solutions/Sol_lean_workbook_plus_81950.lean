-- Prove2me | solution 1 for lean_workbook_plus_81950
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T14:28:18.205788+00:00
-- url     : https://prove2.me/submissions/e561047c-98d7-4585-b6de-2798968aa4d0

import Mathlib.Tactic

theorem solution : ∃ e f : ℕ, f = 5 ^ 2 ∧ e = 7 ^ 4 ∧ e > f ∧ ¬e ∣ f :=
  ⟨7 ^ 4, 5 ^ 2, rfl, rfl, by norm_num, by norm_num⟩
