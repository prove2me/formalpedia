-- Prove2me | Theorems.Thm_lean_workbook_plus_9577
-- name    : lean_workbook_plus_9577
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/ea69adb8-cd33-413e-92a6-edca29897235
-- statement:
--   Prove the inequality $(x^2+3xy+y^2)^2(2x^2+3xy+2y^2)\ge 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9577 (x y : ℝ) : (x^2 + 3 * x * y + y^2)^2 * (2 * x^2 + 3 * x * y + 2 * y^2) ≥ 0   :=  by sorry
