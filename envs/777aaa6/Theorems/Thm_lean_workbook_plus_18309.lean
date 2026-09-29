-- Prove2me | Theorems.Thm_lean_workbook_plus_18309
-- name    : lean_workbook_plus_18309
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/6a936827-59b3-405f-8673-0e469f8871b6
-- statement:
--   Let $a, b> 0$ . Prove that \n $$\frac{a}{b}+ \frac{4b}{a}+\frac{ ab}{a^2+4b^2}\ge\frac{17}{4}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18309 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a / b + 4 * b / a + a * b / (a ^ 2 + 4 * b ^ 2) ≥ 17 / 4   :=  by sorry
