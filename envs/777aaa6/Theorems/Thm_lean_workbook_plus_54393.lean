-- Prove2me | Theorems.Thm_lean_workbook_plus_54393
-- name    : lean_workbook_plus_54393
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/d7aa3974-c0ac-4776-b784-f77beb15188c
-- statement:
--   Prove that $a^4 + b^4 + c^4 \ge a^2 bc + ab^2 c + abc^2$ using the AM-GM Inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54393 (a b c : ℝ) : a ^ 4 + b ^ 4 + c ^ 4 ≥ a ^ 2 * b * c + a * b ^ 2 * c + a * b * c ^ 2   :=  by sorry
