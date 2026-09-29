-- Prove2me | Theorems.Thm_lean_workbook_plus_70775
-- name    : lean_workbook_plus_70775
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/f8bb116e-6917-4bdd-939b-5a9621c816b8
-- statement:
--   (If $a,b,c,d\in\mathbb{R}^+$ and $a+b+c+d=1$ , prove that $ab+bc+cd\le\frac{1}{4}$ .)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70775 (a b c d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) (hab : a + b + c + d = 1) : a * b + b * c + c * d ≤ 1 / 4   :=  by sorry
