-- Prove2me | Theorems.Thm_lean_workbook_plus_80069
-- name    : lean_workbook_plus_80069
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/7b08bb07-cf32-4bf9-8bbc-c400360dbdcf
-- statement:
--   Prove that $ x^3 + y^3 \ge xy(x + y)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80069 : ∀ x y : ℝ, x ^ 3 + y ^ 3 ≥ x * y * (x + y)   :=  by sorry
