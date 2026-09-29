-- Prove2me | Theorems.Thm_lean_workbook_plus_28418
-- name    : lean_workbook_plus_28418
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/f52f24f9-66d5-4a44-bb76-c5881fc26543
-- statement:
--   If $a,b,c>0$ then prove the inequality: $(a+b+c)^3\geq\frac{9}{4}\cdot ((a+b)^2c+((b+c)^2a+(c+a)^2b)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28418 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) ^ 3 ≥ (9 / 4) * ((a + b) ^ 2 * c + (b + c) ^ 2 * a + (c + a) ^ 2 * b)   :=  by sorry
