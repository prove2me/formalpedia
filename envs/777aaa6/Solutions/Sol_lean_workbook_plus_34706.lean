-- Prove2me | solution 1 for lean_workbook_plus_34706
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:17:03.764782+00:00
-- url     : https://prove2.me/submissions/4716668c-88de-4187-9a26-727751cd5931

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℕ → ℝ) (x1 : x 0 = 1 / 2) (xn : ∀ n, x (n + 1) = (x n)^2 + 1) : ∃ f : ℕ → ℝ, ∀ n, x n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
