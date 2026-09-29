-- Prove2me | Theorems.Thm_lean_workbook_plus_75982
-- name    : lean_workbook_plus_75982
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/e019a712-f09a-4782-8292-a57eab220bfa
-- statement:
--   Prove that $(x - 1)(y - 1) \geq 0$ for $x, y \geq 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75982 (x y : ℝ) (hx : x ≥ 1) (hy : y ≥ 1) : (x - 1) * (y - 1) ≥ 0   :=  by sorry
