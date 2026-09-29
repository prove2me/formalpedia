-- Prove2me | Theorems.Thm_lean_workbook_plus_23652
-- name    : lean_workbook_plus_23652
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/8d0c762d-44c7-4853-995b-1b544033e65d
-- statement:
--   Prove that $f(x)=-f(-x)$ for all $x\in\mathbb R$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23652 (f : ℝ → ℝ) (hf: ∀ x, f x + f (-x) = 0) : ∀ x, f x = -f (-x)   :=  by sorry
