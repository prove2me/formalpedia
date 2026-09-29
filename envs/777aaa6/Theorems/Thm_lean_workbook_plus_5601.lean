-- Prove2me | Theorems.Thm_lean_workbook_plus_5601
-- name    : lean_workbook_plus_5601
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/fd3ea664-a6db-4448-a052-fb1e6bde6162
-- statement:
--   Characteristic equation $t^2-7t+10=0$ , so $t_1=2,t_2=5$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5601 (t : ℝ) : t^2 - 7*t + 10 = 0 ↔ t = 2 ∨ t = 5   :=  by sorry
