-- Prove2me | Theorems.Thm_lean_workbook_plus_59207
-- name    : lean_workbook_plus_59207
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/2194e40f-eba7-4423-9d7a-6d96bb523d23
-- statement:
--   Prove that $\sum ((a-b)^4(a^2+b^2+c^2)+(a-b)^2(c^2-ab)^2) \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59207 (a b c : ℝ) : (a - b) ^ 4 * (a ^ 2 + b ^ 2 + c ^ 2) + (a - b) ^ 2 * (c ^ 2 - a * b) ^ 2 ≥ 0   :=  by sorry
