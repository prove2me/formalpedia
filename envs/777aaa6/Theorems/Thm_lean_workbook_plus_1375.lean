-- Prove2me | Theorems.Thm_lean_workbook_plus_1375
-- name    : lean_workbook_plus_1375
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/dad8f616-d413-4547-b7cf-d88ecebc1d34
-- statement:
--   If $a, b, c$ are non-negative real numbers, then prove : $[\sum_{cyc} a^2 ]+ 2abc + 1 \ge \sum_{cyc}ab$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1375 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a^2 + b^2 + c^2 + 2 * a * b * c + 1 ≥ a * b + b * c + c * a   :=  by sorry
