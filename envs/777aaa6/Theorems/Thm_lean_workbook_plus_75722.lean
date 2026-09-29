-- Prove2me | Theorems.Thm_lean_workbook_plus_75722
-- name    : lean_workbook_plus_75722
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/da526b16-6efd-4aff-afc0-dd1f9a0f71be
-- statement:
--   Prove that $2(a-b-c)^2+6(b-\frac{2c}{3})^2\geq 0$ given $a,b,c\in\mathbb{R}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75722 (a b c : ℝ) : (2 * (a - b - c) ^ 2 + 6 * (b - 2 * c / 3) ^ 2) ≥ 0   :=  by sorry
