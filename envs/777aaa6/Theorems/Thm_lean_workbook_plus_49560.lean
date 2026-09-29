-- Prove2me | Theorems.Thm_lean_workbook_plus_49560
-- name    : lean_workbook_plus_49560
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/b1d840fe-8902-4bfe-90b4-802a22767374
-- statement:
--   Prove that $(ab+bc+ca-3)^2 \ge 9(abc-1)$ given $a+b+c=3$ and $a, b, c \in \mathbb{R}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49560 (a b c : ℝ) (ha : a + b + c = 3) : (a * b + b * c + c * a - 3) ^ 2 ≥ 9 * (a * b * c - 1)   :=  by sorry
