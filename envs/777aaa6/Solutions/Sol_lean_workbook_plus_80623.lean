-- Prove2me | solution 1 for lean_workbook_plus_80623
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-17T16:56:59.750965+00:00
-- url     : https://prove2.me/submissions/a434b680-3011-48e5-b8a8-2b360855a8e9

import Mathlib.Tactic

theorem solution (f : ℝ → ℝ) (a b : ℝ) (h : ∀ x, f x = a * x + b) : ∀ x, f x = a * x + b := h
