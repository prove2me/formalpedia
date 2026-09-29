-- Prove2me | Theorems.Thm_lean_workbook_plus_24191
-- name    : lean_workbook_plus_24191
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/f7e2c303-1be4-414b-bb8e-1e506e06278a
-- statement:
--   Let $a,b\in \mathbb{R}$ and $(a+\sqrt{a^2+1})(b+\sqrt{b^2+1})=k$ , where $k>0. $ Prove that $(1+k)(a+b)=(k-1)(\sqrt{a^2+1}+\sqrt{b^2+1}).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24191 (a b k : ℝ) (h₁ : 0 < k) (h₂ : (a + Real.sqrt (a^2 + 1)) * (b + Real.sqrt (b^2 + 1)) = k) : (1 + k) * (a + b) = (k - 1) * (Real.sqrt (a^2 + 1) + Real.sqrt (b^2 + 1))   :=  by sorry
