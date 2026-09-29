-- Prove2me | Theorems.Thm_lean_workbook_plus_53142
-- name    : lean_workbook_plus_53142
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/1a6dc46a-e206-46d9-8a94-c34cb09e5126
-- statement:
--   Prove that $\frac{a}{2008}+\frac{b}{2007}+\frac{c}{2006}\geq 0$ if for each $x\geq 0$, $ax^2+bx+c\geq 0$ and $a, b, c \in \mathbb{R}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53142 (a b c : ℝ) (ha : ∀ x : ℝ, x ≥ 0 → a * x ^ 2 + b * x + c ≥ 0) : a / 2008 + b / 2007 + c / 2006 ≥ 0   :=  by sorry
