-- Prove2me | Theorems.Thm_lean_workbook_plus_4164
-- name    : lean_workbook_plus_4164
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/b23791e3-7a90-4f7b-b6d0-964b6bbad786
-- statement:
--   Prove: $\sum a^2-\sum ab\geq 3.(a-b)(b-c)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4164 {a b c : ℝ} : a^2 + b^2 + c^2 - (a * b + b * c + c * a) ≥ 3 * (a - b) * (b - c)   :=  by sorry
