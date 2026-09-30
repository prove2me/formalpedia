-- Prove2me | solution 1 for lean_workbook_plus_43100
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T02:10:27.475971+00:00
-- url     : https://prove2.me/submissions/01c33684-a0a8-44d8-a0c0-6c9cfa1c5c67

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℕ → ℕ) (h : x 0 = 1 ∧ ∀ n, x (n + 1) = x n + x (n + 2)) : x 2004 % 3 = 1 := by
  obtain ⟨h0, hrec⟩ := h
  have h1 : x 1 = x 0 + x 2 := hrec 0
  have h2 : x 2 = x 1 + x 3 := hrec 1
  omega
