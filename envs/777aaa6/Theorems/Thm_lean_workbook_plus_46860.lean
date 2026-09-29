-- Prove2me | Theorems.Thm_lean_workbook_plus_46860
-- name    : lean_workbook_plus_46860
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/3e9adbe9-8422-4bbf-b0f9-704ab1e9c49c
-- statement:
--   Let $a,b,c\ge 0$ and $\frac{ab}{1+a+b}+\frac{bc}{1+b+c}+\frac{ca}{1+c+a}=1. $ Prove that $$1+a+b+c \ge 4abc$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46860 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (habc : a * b * c ≠ 0) (h : (a * b / (1 + a + b)) + (b * c / (1 + b + c)) + (c * a / (1 + c + a)) = 1) : 1 + a + b + c ≥ 4 * a * b * c   :=  by sorry
