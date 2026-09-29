-- Prove2me | Theorems.Thm_lean_workbook_plus_64572
-- name    : lean_workbook_plus_64572
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/bc68166e-ffd9-4e16-98a0-1b3c59007439
-- statement:
--   If $f(\mathbb{R}) = \{0\}$, then $f(x) = 0$ for all $x \in \mathbb{R}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64572 (f : ℝ → ℝ) (h : Set.range f = {0}) : ∀ x, f x = 0   :=  by sorry
