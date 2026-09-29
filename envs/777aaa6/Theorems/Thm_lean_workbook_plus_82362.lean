-- Prove2me | Theorems.Thm_lean_workbook_plus_82362
-- name    : lean_workbook_plus_82362
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/73e76b92-27e0-43fc-984e-2d7b9dc9e3e1
-- statement:
--   If $a, b, c>0$ prove or disprove that $\frac{a+b-c}{a+b+3c}+\frac{b+c-a}{3a+b+c}+\frac{c+a-b}{a+3b+c}\geq\frac{3}{5}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82362 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b - c) / (a + b + 3 * c) + (b + c - a) / (3 * a + b + c) + (c + a - b) / (a + 3 * b + c) ≥ 3 / 5   :=  by sorry
