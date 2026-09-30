-- Prove2me | solution 1 for lean_workbook_plus_34622
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T02:10:26.119176+00:00
-- url     : https://prove2.me/submissions/2f89dd2a-f2ee-48cb-93a6-b3a223486581

import Mathlib.Analysis.Complex.Basic

theorem solution  (x : ℝ)
  (h₀ : x = 18 / 1991)
  : ∃ (a : ℕ → ℕ),
    ∀ (k : ℕ),
      (a k) = 0 ∨ (a k) = 1 ∨ (a k) = 2 ∧
    ∑' k : ℕ, (a k) / 3^k = x ∧
    ∑' k : ℕ, (a k) / 2^k = 5 / 128 := by
  refine ⟨fun _ => 0, fun k => ?_⟩
  left
  rfl
