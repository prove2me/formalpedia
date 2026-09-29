-- Prove2me | Theorems.Thm_lean_workbook_plus_11395
-- name    : lean_workbook_plus_11395
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/83a48525-217f-45f9-a8bb-ea9f701f46e6
-- statement:
--   prove that: $\frac{1}{a} + \frac{1}{b} + \frac{1}{c} \ge \frac{9}{{a + b + c}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11395 {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0) : 1 / a + 1 / b + 1 / c ≥ 9 / (a + b + c)   :=  by sorry
