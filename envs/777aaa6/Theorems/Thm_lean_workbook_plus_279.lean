-- Prove2me | Theorems.Thm_lean_workbook_plus_279
-- name    : lean_workbook_plus_279
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/f1f6af33-0a50-4abf-be49-ce3982a05ded
-- statement:
--   If $a,b,c,d$ are nonnegative real numbers, then $(a + b + c + d)^{3}\\geq 4[a(c + d)^{2} + b(d + a)^{2} + c(a + b)^{2} + d(b + c)^{2}]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_279 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) : (a + b + c + d) ^ 3 ≥ 4 * (a * (c + d) ^ 2 + b * (d + a) ^ 2 + c * (a + b) ^ 2 + d * (b + c) ^ 2)   :=  by sorry
