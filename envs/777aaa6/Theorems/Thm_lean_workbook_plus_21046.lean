-- Prove2me | Theorems.Thm_lean_workbook_plus_21046
-- name    : lean_workbook_plus_21046
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/56b20e5c-4992-49f8-83d5-c9de78f6e07e
-- statement:
--   For all positive real numbers $a, b,c.$ Prove the folllowing inequality $$\frac{a}{c+5b}+\frac{b}{a+5c}+\frac{c}{b+5a}\geq\frac{1}{2}.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21046 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (c + 5 * b) + b / (a + 5 * c) + c / (b + 5 * a)) ≥ 1 / 2   :=  by sorry
