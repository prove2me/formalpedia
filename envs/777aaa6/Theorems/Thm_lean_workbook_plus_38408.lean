-- Prove2me | Theorems.Thm_lean_workbook_plus_38408
-- name    : lean_workbook_plus_38408
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/99a8e2cf-dd60-47bd-9a96-146fc9f01afb
-- statement:
--   $\Rightarrow 1 \geq 8abc\Rightarrow abc\leq \frac{1}{8}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38408 (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 ≥ 8 * a * b * c → a * b * c ≤ 1 / 8   :=  by sorry
