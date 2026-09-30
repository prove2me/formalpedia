-- Prove2me | solution 1 for lean_workbook_plus_49747
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:13:30.845499+00:00
-- url     : https://prove2.me/submissions/40a5887a-ea11-4a24-9ef4-b6835d41fdda

import Mathlib.Analysis.Complex.Basic

theorem solution (a b : ℝ) (h₁ : a ≠ 24) (h₂ : b = 24 * (a - 12) / (a - 24)) : b = 24 * (a - 12) / (a - 24) := h₂
