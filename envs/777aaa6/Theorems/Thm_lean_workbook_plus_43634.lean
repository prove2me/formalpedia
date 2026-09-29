-- Prove2me | Theorems.Thm_lean_workbook_plus_43634
-- name    : lean_workbook_plus_43634
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/29f0f237-3d2e-4e09-9c51-26294c73d25e
-- statement:
--   Find all functions $f: \mathbb{R} \rightarrow \mathbb{R}$ such that $f(x+y) = f(x) + y$ for all $x, y \in \mathbb{R}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43634 (f : ℝ → ℝ): (∀ x y, f (x + y) = f x + y) ↔ ∃ a, ∀ x, f x = x + a   :=  by sorry
