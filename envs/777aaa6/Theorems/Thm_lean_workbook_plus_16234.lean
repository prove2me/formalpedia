-- Prove2me | Theorems.Thm_lean_workbook_plus_16234
-- name    : lean_workbook_plus_16234
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/5ab57d08-50ca-4ccd-83a8-c237bd0fa0d4
-- statement:
--   $ \sqrt {a} \le \frac {1 + a}{2}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16234 (a : ℝ) (ha : 0 ≤ a) : Real.sqrt a ≤ (1 + a) / 2   :=  by sorry
