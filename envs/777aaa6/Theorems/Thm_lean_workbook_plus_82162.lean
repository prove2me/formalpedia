-- Prove2me | Theorems.Thm_lean_workbook_plus_82162
-- name    : lean_workbook_plus_82162
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/1cd39c44-c318-4961-8059-ca1fb016dfa8
-- statement:
--   Prove that $\frac 12 \left( (a-b)^2 + (b-c)^2 + (c-a)^2 \right) \geq 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82162 {a b c : ℝ} : 0.5 * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) ≥ 0   :=  by sorry
