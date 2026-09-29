-- Prove2me | Theorems.Thm_lean_workbook_plus_20585
-- name    : lean_workbook_plus_20585
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/b3637540-9fe3-453d-844e-cba2de540b27
-- statement:
--   And solution $\boxed{f(x)=c\quad\forall x}$ whatever is $c\in\mathbb R$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20585 (x : ℝ) (f : ℝ → ℝ) (hf: f x = f 0) : f x = f 0   :=  by sorry
