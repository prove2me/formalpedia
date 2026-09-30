-- Prove2me | solution 1 for lean_workbook_plus_27888
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:55:57.237774+00:00
-- url     : https://prove2.me/submissions/9326b53a-baca-4d71-9f19-9048b2d77636

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) : abs a + abs b + abs c + abs (a + b + c) ≥ abs (a + b) + abs (a + c) + abs (b + c) := by
  rcases abs_cases a with ⟨ha, _⟩ <;> rcases abs_cases b with ⟨hb, _⟩ <;>
  rcases abs_cases c with ⟨hc, _⟩ <;> rcases abs_cases (a + b + c) with ⟨habc, _⟩ <;>
  rcases abs_cases (a + b) with ⟨hab, _⟩ <;> rcases abs_cases (a + c) with ⟨hac, _⟩ <;>
  rcases abs_cases (b + c) with ⟨hbc, _⟩ <;> linarith
