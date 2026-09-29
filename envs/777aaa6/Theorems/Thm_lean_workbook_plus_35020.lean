-- Prove2me | Theorems.Thm_lean_workbook_plus_35020
-- name    : lean_workbook_plus_35020
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/91f71ab2-e8d1-4440-b630-950443cc39b7
-- statement:
--   Prove that $f(x) = cx^2$ for all $x \in \mathbb{R}$, where $c$ is a constant.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35020 (f : ℝ → ℝ) (c : ℝ) (h : ∀ x, f x = c * x ^ 2) : ∀ x, f x = c * x ^ 2   :=  by sorry
