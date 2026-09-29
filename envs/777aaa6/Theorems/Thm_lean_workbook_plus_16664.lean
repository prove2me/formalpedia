-- Prove2me | Theorems.Thm_lean_workbook_plus_16664
-- name    : lean_workbook_plus_16664
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/b8f88e2f-daf2-42c7-ae36-08384a3cafc0
-- statement:
--   Let $a$ , $b$ be real positive numbers such that $a\geq 2b$ Prove that $\frac{a^2}{b} + \frac{b^2}{a}$ $\geq$ $\frac{9a}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16664 (a b : ℝ) (hab : a ≥ 2 * b) (ha : a > 0) (hb : b > 0) : a^2 / b + b^2 / a ≥ 9 * a / 4   :=  by sorry
