-- Prove2me | Theorems.Thm_lean_workbook_plus_77445
-- name    : lean_workbook_plus_77445
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/305760e7-98db-471e-9a9e-8f670a79688f
-- statement:
--   $\sin{3x}=0\Longrightarrow x=\dfrac{n\pi}{3}, n\in\mathbb{Z}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77445 (x : ℝ) : sin (3 * x) = 0 ↔ ∃ n : ℤ, x = n * π / 3   :=  by sorry
