-- Prove2me | Theorems.Thm_lean_workbook_plus_82330
-- name    : lean_workbook_plus_82330
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/057f681f-3e88-4372-9ebc-b2f9709ad5dd
-- statement:
--   Find all functions $f:R\rightarrow R$ such that $f(x-f(y))=1-x-y$ , for all $x,y\in{\mathbb{R}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82330 (f : ℝ → ℝ): (∀ x y, f (x - f y) = 1 - x - y) ↔ ∀ x, f x = 1 / 2 - x   :=  by sorry
