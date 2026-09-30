-- Prove2me | solution 1 for lean_workbook_plus_29686
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:07:14.64158+00:00
-- url     : https://prove2.me/submissions/b41a56cf-2893-48cf-b8df-fa8f3f58c4f9

import Mathlib.Analysis.Complex.Basic

theorem solution {n : ℕ} (a : ℕ → ℕ) (h₀ : ∀ i, 0 < a i) (h₁ : ∀ i j, i ≠ j → (a i, a j) = (i, j)) : ∀ i, a i = i := by
  intro i
  have h := h₁ i (i + 1) (by omega)
  exact (Prod.mk.injEq _ _ _ _ ▸ h).1
