-- Prove2me | Theorems.Thm_lean_workbook_plus_49259
-- name    : lean_workbook_plus_49259
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/444e1bb6-eb04-4e7a-bb24-3ed402ba10fe
-- statement:
--   Let $a+b = x, ab = y$ . Then $a^2+b^2 = a+b \implies x^2-2y = x$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49259 (a b x y : ℝ) (h₁ : a + b = x) (h₂ : a * b = y) (h₃ : a^2 + b^2 = a + b) : x^2 - 2*y = x   :=  by sorry
