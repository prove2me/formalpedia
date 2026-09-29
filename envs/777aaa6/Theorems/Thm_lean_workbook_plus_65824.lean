-- Prove2me | Theorems.Thm_lean_workbook_plus_65824
-- name    : lean_workbook_plus_65824
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/81e91355-e461-44b2-b65a-1ef392edb58c
-- statement:
--   Prove that the zeta function \n $\zeta(x) = \frac{1}{1^{x}}+\frac{1}{2^{x}}+\frac{1}{3^{x}}+...$ \n converges when $x\geq 2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65824 (x : ℝ) (h : x ≥ 2) : ∃ y, ∑' n : ℕ, (1/(n^x) : ℝ) = y   :=  by sorry
