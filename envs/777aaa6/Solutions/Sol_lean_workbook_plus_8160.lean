-- Prove2me | solution 1 for lean_workbook_plus_8160
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:41:08.857774+00:00
-- url     : https://prove2.me/submissions/31cef218-9fd5-432d-b91d-9a3e0d82c7d6

import Mathlib.Analysis.Complex.Basic

theorem solution : ∃ f g : ℝ → ℝ, ∀ x, f x = -x ∧ g x = -x :=
  ⟨fun x => -x, fun x => -x, fun _ => ⟨rfl, rfl⟩⟩
