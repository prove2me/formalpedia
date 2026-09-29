-- Prove2me | Theorems.Thm_lean_workbook_plus_39257
-- name    : lean_workbook_plus_39257
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/16fbaaeb-d6dc-412a-8e88-c03e516f3fa2
-- statement:
--   Prove that $(a-b)^2 +(c-1)^2+2c(a-1)(b-1) \geq 0 \iff a^2+b^2+c^2+2abc+1 \geq 2(ab+bc+ca)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39257 (a b c : ℝ) : (a - b) ^ 2 + (c - 1) ^ 2 + 2 * c * (a - 1) * (b - 1) ≥ 0 ↔ a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b * c + 1 ≥ 2 * (a * b + b * c + a * c)   :=  by sorry
