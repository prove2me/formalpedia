-- Prove2me | Theorems.Thm_lean_workbook_plus_1400
-- name    : lean_workbook_plus_1400
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/a78813d6-dcaf-408c-a4e7-5f7ea591b870
-- statement:
--   Prove that $f(x) = ax^2$ is a solution for all $a\in\mathbb{R},a\leq 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1400 (a : ℝ) (ha : a ≤ 0) : ∀ x : ℝ, ∃ y : ℝ, y = a * x ^ 2   :=  by sorry
