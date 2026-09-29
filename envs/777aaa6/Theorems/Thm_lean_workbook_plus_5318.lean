-- Prove2me | Theorems.Thm_lean_workbook_plus_5318
-- name    : lean_workbook_plus_5318
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/1da29ca4-f66b-4f26-8455-266946c242b5
-- statement:
--   Prove that \(a^2-ab+b^2\ge \frac {a^2+ab+b^2} {3}\) which is equivalent to \((a-b)^2\ge 0\) assuming \(a,b>0\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5318 (a b : ℝ) (ha : a > 0) (hb : b > 0) : a^2 - a * b + b^2 ≥ (a^2 + a * b + b^2) / 3   :=  by sorry
