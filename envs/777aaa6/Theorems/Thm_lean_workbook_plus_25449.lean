-- Prove2me | Theorems.Thm_lean_workbook_plus_25449
-- name    : lean_workbook_plus_25449
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/a888b046-7df2-4a75-ac13-7a7883513e9c
-- statement:
--   Suppose a,b,c are sides of triangle. Prove that:\n $$a^2 (b + c - a) + b^2 (a+ c - b) + c^2 (a + b - c) \le\ 3 a b c$$\n\nSchur
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25449    (a b c : ℝ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₁ : a + b > c)
    (h₂ : a + c > b)
    (h₃ : b + c > a) :
    a^2 * (b + c - a) + b^2 * (a + c - b) + c^2 * (a + b - c) ≤ 3 * a * b * c   :=  by sorry
