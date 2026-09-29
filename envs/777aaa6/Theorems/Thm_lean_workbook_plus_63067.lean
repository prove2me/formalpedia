-- Prove2me | Theorems.Thm_lean_workbook_plus_63067
-- name    : lean_workbook_plus_63067
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/c06f8d68-432e-4f78-9686-e79482b85c78
-- statement:
--   $f(x)=f(-x)$ $\implies$ $f(x-1)=f(1-x)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63067 (f : ℝ → ℝ) (x : ℝ) (h : ∀ x, f x = f (-x)) : ∀ x, f (x - 1) = f (1 - x)   :=  by sorry
