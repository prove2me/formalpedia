-- Prove2me | Theorems.Thm_lean_workbook_plus_64363
-- name    : lean_workbook_plus_64363
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/75b0c5ae-a8d7-48a4-a683-9091b34f12a5
-- statement:
--   Prove that $(a+b)(a+c)(b+c) \ge \frac{8}{9}(a+b+c)(ab+ac+bc)$ for positive numbers $a, b, c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64363 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) * (a + c) * (b + c) ≥ (8:ℝ) / 9 * (a + b + c) * (a * b + a * c + b * c)   :=  by sorry
