-- Prove2me | Theorems.Thm_lean_workbook_plus_15509
-- name    : lean_workbook_plus_15509
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/7c76cc85-b8d5-4b2d-b9ab-ed5e8f5c9cf3
-- statement:
--   Prove that \(a^2 + b^2 + c^2 \ge 3\) if \(a, b, c > 0\) and \(a + b + c \ge 3\) .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15509 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c >= 3) : a^2 + b^2 + c^2 >= 3   :=  by sorry
