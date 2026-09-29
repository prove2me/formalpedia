-- Prove2me | Theorems.Thm_lean_workbook_plus_26914
-- name    : lean_workbook_plus_26914
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/4cc9fdf8-f085-4e2b-ad79-78b43a4e9dc3
-- statement:
--   Prove that:\n\n$ \frac{1}{(a+b)^2} + \frac{1}{(b+c)^2} + \frac{1}{(c+a)^2} \ge \frac{3}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26914 : ∀ a b c : ℝ, (1 / (a + b) ^ 2 + 1 / (b + c) ^ 2 + 1 / (c + a) ^ 2) ≥ 3 / 4   :=  by sorry
