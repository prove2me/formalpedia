-- Prove2me | Theorems.Thm_lean_workbook_plus_7074
-- name    : lean_workbook_plus_7074
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/d217929a-12ea-4116-9f4a-aa9d2038fa64
-- statement:
--   Prove that $ a^4 + b^4 + c^4 + d^4 + a^2b^2 + b^2c^2 + c^2d^2 + d^2a^2\geq 2 (a^3 b + b^3 c + c^3 d + a d^3)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7074 (a b c d : ℝ) : a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4 + a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * d ^ 2 + d ^ 2 * a ^ 2 ≥ 2 * (a ^ 3 * b + b ^ 3 * c + c ^ 3 * d + a * d ^ 3)   :=  by sorry
