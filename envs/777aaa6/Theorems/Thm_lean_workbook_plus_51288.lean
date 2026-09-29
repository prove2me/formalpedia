-- Prove2me | Theorems.Thm_lean_workbook_plus_51288
-- name    : lean_workbook_plus_51288
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/e267c4c1-9209-4af4-9475-ff508857df1b
-- statement:
--   Prove $(t-2)(t+1)(8t-7)\ge 0$ for $t\ge 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51288 (t : ℝ) (h₁ : t ≥ 2) : (t - 2) * (t + 1) * (8 * t - 7) ≥ 0   :=  by sorry
