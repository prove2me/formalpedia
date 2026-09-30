-- Prove2me | solution 1 for lean_workbook_plus_21837
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:41:55.021457+00:00
-- url     : https://prove2.me/submissions/37c32642-3e2f-4822-b423-1468a7f80bf1

import Mathlib.Analysis.Complex.Basic

theorem solution : ∃ a : ℕ → ℚ, a 0 = 1 / 1260 ∧ a 1 = 1 / 840 ∧ a 2 = 1 / 630 ∧ a 3 = 1 / 504 ∧ a 4 = 1 / 420 ∧ a 5 = 1 / 360 ∧ a 6 = 1 / 315 ∧ a 7 = 1 / 280 ∧ a 8 = 1 / 252 := by
  refine ⟨fun n => match n with
    | 0 => 1 / 1260
    | 1 => 1 / 840
    | 2 => 1 / 630
    | 3 => 1 / 504
    | 4 => 1 / 420
    | 5 => 1 / 360
    | 6 => 1 / 315
    | 7 => 1 / 280
    | 8 => 1 / 252
    | _ => 0, ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
