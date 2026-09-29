-- Prove2me | Theorems.Thm_lean_workbook_plus_36125
-- name    : lean_workbook_plus_36125
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/a01e9374-0349-44c9-a322-88cc268653d3
-- statement:
--   define the polynomial $G(x)=a_{0}x+a_{1}x^2/2+a_{2}x^3/3+.....+a_{n}x^{n+1}/(n+1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36125 (n : ℕ) (a : ℕ → ℝ) (x : ℝ) : ∃ y, y = (∑ i in Finset.range (n+1), (a i * x ^ (i + 1) / (i + 1)))   :=  by sorry
