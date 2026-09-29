-- Prove2me | Theorems.Thm_lean_workbook_plus_57735
-- name    : lean_workbook_plus_57735
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/f7d531f2-9155-467b-bd6b-6cb910aae8fd
-- statement:
--   Find all functions $f: \mathbb{R} \rightarrow \mathbb{R}$ such that for all $x, y \in \mathbb{R}$, $f(x^2 - y) = f(y) - f(x)^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57735 (f : ℝ → ℝ): (∀ x y, f (x ^ 2 - y) = f y - f x ^ 2) ↔ ∀ x, f x = 0   :=  by sorry
