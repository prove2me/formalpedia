-- Prove2me | solution 1 for lean_workbook_plus_18661
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:46:02.320498+00:00
-- url     : https://prove2.me/submissions/c89df6ff-c827-4f09-a76d-823993ec87ac

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c: ℝ) : abs a + abs b + abs c + abs (a + b + c) ≥ abs (a + b) + abs (b + c) + abs (a + c) := by
  rcases abs_cases a with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
  rcases abs_cases b with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
  rcases abs_cases c with ⟨h3, _⟩ | ⟨h3, _⟩ <;>
  rcases abs_cases (a + b) with ⟨h4, _⟩ | ⟨h4, _⟩ <;>
  rcases abs_cases (b + c) with ⟨h5, _⟩ | ⟨h5, _⟩ <;>
  rcases abs_cases (a + c) with ⟨h6, _⟩ | ⟨h6, _⟩ <;>
  rcases abs_cases (a + b + c) with ⟨h7, _⟩ | ⟨h7, _⟩ <;>
  linarith
