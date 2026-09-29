-- Prove2me | Theorems.Thm_lean_workbook_plus_81363
-- name    : lean_workbook_plus_81363
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/cddd897e-bd39-41d4-98bc-7130633d5c0d
-- statement:
--   Let $a,\ b,\ c,\ d$ be real numbers such that $(a-1)(b-1)(c-1)(d-1)=1$ . For $a\geq 2,\ b\geq 2,\ c\geq 2,\ d\geq 2$ , prove that $\ \frac{1}{a}+\frac{1}{b}+\frac{1}{c}+\frac{1}{d}\leq2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81363 (a b c d : ℝ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d) (habc : (a - 1) * (b - 1) * (c - 1) * (d - 1) = 1) : 1 / a + 1 / b + 1 / c + 1 / d ≤ 2   :=  by sorry
