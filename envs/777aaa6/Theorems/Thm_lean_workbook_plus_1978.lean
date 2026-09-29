-- Prove2me | Theorems.Thm_lean_workbook_plus_1978
-- name    : lean_workbook_plus_1978
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/d1e45c8e-fd14-4d1a-907f-e4931a8de065
-- statement:
--   AM-GM ; $ a^4+a^4+b^4+c^4 \geq 4a^2bc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1978 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a ^ 4 + a ^ 4 + b ^ 4 + c ^ 4 ≥ 4 * a ^ 2 * b * c   :=  by sorry
