-- Prove2me | solution 1 for lean_workbook_plus_53063
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:47:01.7997+00:00
-- url     : https://prove2.me/submissions/bb8098fa-5415-466c-af2b-193f743b5cb7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℕ → ℝ) (a1 : a 0 = 5) (a2 : a 1 = 3) : ∃ f : ℕ → ℝ, ∀ n, a n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
