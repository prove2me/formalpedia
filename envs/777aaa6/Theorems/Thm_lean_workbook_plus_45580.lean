-- Prove2me | Theorems.Thm_lean_workbook_plus_45580
-- name    : lean_workbook_plus_45580
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/2b455e26-a4e2-4d94-81f6-17b2c038cb15
-- statement:
--   Prove that $(a+d)^2+(b+e)^2+(c+f)^2 \ge \sum_{sym}ab=(a+d)(b+e)+(b+e)(c+f)+(c+f)(a+d)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45580 (a b c d e f : ℝ) : (a + d) ^ 2 + (b + e) ^ 2 + (c + f) ^ 2 ≥ (a + d) * (b + e) + (b + e) * (c + f) + (c + f) * (a + d)   :=  by sorry
