-- Prove2me | Theorems.Thm_lean_workbook_plus_14632
-- name    : lean_workbook_plus_14632
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/57a2bd00-3353-4e7f-8d34-349b02e2e93d
-- statement:
--   Find all functions $f: \mathbb{R} \rightarrow \mathbb{R}$ such that $(t+1)f(1+xy) - f(x+y) = f(x+1)f(y+1)$ for all $x, y \in \mathbb{R}$, where $t \neq 1$ is a fixed real number.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14632 (t : ℝ) (ht : t ≠ 1) : { f : ℝ → ℝ | (t + 1) * f (1 + x * y) - f (x + y) = f (x + 1) * f (y + 1) } = { f : ℝ → ℝ | ∃ k :ℝ, ∀ x : ℝ, f x = k * x + (1 - k) }   :=  by sorry
