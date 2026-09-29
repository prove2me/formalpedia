-- Prove2me | Theorems.Thm_lean_workbook_plus_20622
-- name    : lean_workbook_plus_20622
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/4b1978bb-77df-4183-9957-909c708bc3f5
-- statement:
--   Find all continuous functions $f:\mathbb{R}\to\mathbb{R}$ which satisfy $f(2022x)-f(2021x)=674x$ for all $x\in\mathbb{R}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20622 (f : ℝ → ℝ) (hf: Continuous f) (h : ∀ x, f (2022 * x) - f (2021 * x) = 674 * x) : ∃ a b, f x = a * x + b   :=  by sorry
