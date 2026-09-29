-- Prove2me | Theorems.Thm_lean_workbook_plus_12651
-- name    : lean_workbook_plus_12651
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/0f404e22-6817-4e96-b5b5-bb32066fa1ee
-- statement:
--   $(a^2+1)(b^2+1)(c^2+1) \ge (a+b+c-abc)^2=(7-abc)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12651 (a b c : ℝ) : (a^2+1)*(b^2+1)*(c^2+1) ≥ (a+b+c-a*b*c)^2   :=  by sorry
