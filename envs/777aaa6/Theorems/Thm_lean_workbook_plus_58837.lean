-- Prove2me | Theorems.Thm_lean_workbook_plus_58837
-- name    : lean_workbook_plus_58837
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/601872ff-48b5-4d96-a8b3-dc6d54ebb71f
-- statement:
--   Since $[f(x)]^2 = 4$ , for all $x_0 \in \mathbb{R}$ , either $f(x_0)=2$ or $f(x_0) = -2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58837 (f : ℝ → ℝ) (hx: ∀ x, (f x)^2 = 4) : ∀ x, (f x = 2 ∨ f x = -2)   :=  by sorry
