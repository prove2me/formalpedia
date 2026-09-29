-- Prove2me | Theorems.Thm_lean_workbook_plus_4073
-- name    : lean_workbook_plus_4073
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/0e618ee0-9d51-42f2-bea0-e909db1215d6
-- statement:
--   Let $a$ , $b$ be real positive numbers such that $a\geq 2b$ Prove that $\frac{a^2}{b} + \frac{b^2}{a}$ $\geq$ $\frac{9a}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4073 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≥ 2 * b) : a^2 / b + b^2 / a ≥ 9 * a / 4   :=  by sorry
