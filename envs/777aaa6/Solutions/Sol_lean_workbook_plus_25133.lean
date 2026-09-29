-- Prove2me | solution 1 for lean_workbook_plus_25133
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:27:07.969359+00:00
-- url     : https://prove2.me/submissions/fb3a5938-2ff6-4471-950a-018f4c005c6e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (w : ℕ → ℝ) (F : ℕ → ℝ) (h₁ : ∀ n, F n = (w n)^2 + (w (n-1))^2 - 4 * w n * w (n-1)) (h₂ : ∀ n, n ≥ 2 → F n - F (n-1) = (w n - w (n-2)) * (w n + w (n-2) - 4 * w (n-1))) : ∀ n, n ≥ 2 → F n - F (n-1) = (w n - w (n-2)) * (w n + w (n-2) - 4 * w (n-1)) := by
  (intros; simp_all)
