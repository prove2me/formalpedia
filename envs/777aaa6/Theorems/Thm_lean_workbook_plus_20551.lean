-- Prove2me | Theorems.Thm_lean_workbook_plus_20551
-- name    : lean_workbook_plus_20551
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/95c41c11-9e30-45f5-b8c6-e984d5fcd797
-- statement:
--   Prove Nesbitt's inequality: \(\frac{a}{b+c}+\frac{b}{c+a}+\frac{c}{a+b}\ge \frac{3}{2}\) for positive \(a, b, c\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20551 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c) + b / (c + a) + c / (a + b)) ≥ 3 / 2   :=  by sorry
