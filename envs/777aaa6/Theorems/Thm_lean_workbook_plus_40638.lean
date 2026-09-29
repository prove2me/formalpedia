-- Prove2me | Theorems.Thm_lean_workbook_plus_40638
-- name    : lean_workbook_plus_40638
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/00ad4ac8-545d-42dd-98f1-7fe411ef0e8e
-- statement:
--   Let $a, b$ and $c$ denote positive real numbers. Prove that $\frac{a}{c}+\frac{c}{b}\ge \frac{4a}{a + b}$ .\nWhen does equality hold?\n\n(Walther Janous)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40638 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / c + c / b) ≥ 4 * a / (a + b)   :=  by sorry
