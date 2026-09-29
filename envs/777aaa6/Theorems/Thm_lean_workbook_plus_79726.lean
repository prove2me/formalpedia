-- Prove2me | Theorems.Thm_lean_workbook_plus_79726
-- name    : lean_workbook_plus_79726
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/f3e60d95-9401-48d2-9209-a0af35c5e1b0
-- statement:
--   If $f(0)=2$, $f(x)=2 \quad \forall x\in \mathbb{R}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79726 (f : ℝ → ℝ) (hf: f 0 = 2) (h : ∀ x, f x = 2) : f x = 2   :=  by sorry
