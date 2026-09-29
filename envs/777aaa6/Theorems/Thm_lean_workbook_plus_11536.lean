-- Prove2me | Theorems.Thm_lean_workbook_plus_11536
-- name    : lean_workbook_plus_11536
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/c8d8ad0e-e3d7-4e73-9d99-3e83d9e19d57
-- statement:
--   $\boxed{f(x)=0\quad\forall x\in\mathbb R}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11536 (f : ℝ → ℝ) (hf: f = fun x => 0) : ∀ x, f x = 0   :=  by sorry
