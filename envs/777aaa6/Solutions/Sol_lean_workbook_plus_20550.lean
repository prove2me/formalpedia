-- Prove2me | solution 1 for lean_workbook_plus_20550
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:36:00.304368+00:00
-- url     : https://prove2.me/submissions/351eb287-ce05-40d8-affc-4ba0c6a1deb1

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) : 2 * |a + b + c| ≤ |a + b| + |b + c| + |c + a| := by
  rcases abs_cases (a + b + c) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
  rcases abs_cases (a + b) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
  rcases abs_cases (b + c) with ⟨h3, _⟩ | ⟨h3, _⟩ <;>
  rcases abs_cases (c + a) with ⟨h4, _⟩ | ⟨h4, _⟩ <;>
  linarith
