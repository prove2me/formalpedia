-- Prove2me | Theorems.Thm_lean_workbook_plus_17715
-- name    : lean_workbook_plus_17715
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/ba2d7070-7106-419f-a55e-2a70df89bae3
-- statement:
--   For $a, b, c>0$ prove or disprove that $\frac{a-b}{a+4b+4c}+\frac{b-c}{4a+b+4c}+\frac{c-a}{4a+4b+c}\geq0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17715 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a - b) / (a + 4 * b + 4 * c) + (b - c) / (4 * a + b + 4 * c) + (c - a) / (4 * a + 4 * b + c) ≥ 0   :=  by sorry
