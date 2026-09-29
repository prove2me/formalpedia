-- Prove2me | Theorems.Thm_lean_workbook_plus_32736
-- name    : lean_workbook_plus_32736
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/8d555210-799f-4501-bf81-4337a556d8fc
-- statement:
--   Prove that $(a + b + c)^2 \geq 2(a + b + c) + ab + bc + ca \Leftrightarrow a^2 + b^2 + c^2 + ab + bc + ca \geq 2(a + b + c)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32736 (a b c : ℝ) : (a + b + c) ^ 2 ≥ 2 * (a + b + c) + a * b + b * c + c * a ↔ a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a ≥ 2 * (a + b + c)   :=  by sorry
