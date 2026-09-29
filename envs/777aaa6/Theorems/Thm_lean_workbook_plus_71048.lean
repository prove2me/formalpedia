-- Prove2me | Theorems.Thm_lean_workbook_plus_71048
-- name    : lean_workbook_plus_71048
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/48631d6f-2f56-449e-aee2-dd82134ed8b4
-- statement:
--   $f(x)=1,\quad\forall x\in\mathbb{R}$ ,
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71048 (f : ℝ → ℝ) (h : ∀ x, f x = 1) : Set.range f = {1}   :=  by sorry
