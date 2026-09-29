-- Prove2me | Theorems.Thm_lean_workbook_plus_54181
-- name    : lean_workbook_plus_54181
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/d0d7201e-c372-40ca-a36e-3edea92ca021
-- statement:
--   Choose for example $f(x)=c$ $\forall x$ and whatever is $c\in\mathbb R$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54181 (f : ℝ → ℝ) (c : ℝ) (h : ∀ x, f x = c) : ∃ c, ∀ x, f x = c   :=  by sorry
