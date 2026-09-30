-- Prove2me | solution 1 for lean_workbook_plus_11330
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:41:57.069925+00:00
-- url     : https://prove2.me/submissions/1c5a11eb-856e-40a6-8ecb-b8c8c3acdf65

import Mathlib.Analysis.Complex.Basic

theorem solution : ∃ f : ℕ → ℕ, f 0 = 0 ∧ f 1 = 1 ∧ f 2 = 8 ∧ f 3 = 49 ∧ f 4 = 288 ∧ f 5 = 1681 ∧ f 6 = 9800 ∧ f 7 = 57121 := by
  refine ⟨fun n => match n with
    | 0 => 0
    | 1 => 1
    | 2 => 8
    | 3 => 49
    | 4 => 288
    | 5 => 1681
    | 6 => 9800
    | 7 => 57121
    | _ => 0, ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
