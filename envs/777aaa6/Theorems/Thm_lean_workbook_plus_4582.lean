-- Prove2me | Theorems.Thm_lean_workbook_plus_4582
-- name    : lean_workbook_plus_4582
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/c1f2962a-3f86-4fb2-8835-bc353c6e99d7
-- statement:
--   Let $a,\ b,\ c,\ d$ be real numbers such that $(a-1)(b-1)(c-1)(d-1)=1$ . For $a\geq 2,\ b\geq 2,\ c\geq 2,\ d\geq 2$ , prove that $\ \frac{1}{a}+\frac{1}{b}+\frac{1}{c}+\frac{1}{d}\geq 2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4582 (a b c d : ℝ) (ha : a ≥ 2) (hb : b ≥ 2) (hc : c ≥ 2) (hd : d ≥ 2) (habc : (a - 1) * (b - 1) * (c - 1) * (d - 1) = 1) : 1 / a + 1 / b + 1 / c + 1 / d ≥ 2   :=  by sorry
