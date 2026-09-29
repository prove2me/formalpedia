-- Prove2me | Theorems.Thm_lean_workbook_plus_20179
-- name    : lean_workbook_plus_20179
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/b2ad0fee-7b3d-483d-b96b-22a422c31ca6
-- statement:
--   Let $b-a=n-m=k>0$ so $b=a+k,n=m+k$ and $a+b\geq m+n\Longleftrightarrow a\geq m$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20179 (a b : ℝ) (m n : ℝ) (k : ℝ) (h₁ : b - a = k) (h₂ : n - m = k) (h₃ : a + b ≥ m + n) : a ≥ m   :=  by sorry
