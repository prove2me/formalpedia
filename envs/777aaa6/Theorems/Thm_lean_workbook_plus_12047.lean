-- Prove2me | Theorems.Thm_lean_workbook_plus_12047
-- name    : lean_workbook_plus_12047
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/32f0286e-59a8-4f5f-a2d2-e92aeaa037c1
-- statement:
--   (x^{2}+1)(y^{2}+1) \geq (xy+1)^{2}$ , $ x ,y \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12047 (x y : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) : (x^2 + 1) * (y^2 + 1) ≥ (x * y + 1)^2   :=  by sorry
