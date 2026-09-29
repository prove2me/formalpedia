-- Prove2me | Theorems.Thm_lean_workbook_plus_9901
-- name    : lean_workbook_plus_9901
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/c698c22f-4db0-436b-b316-f0c2b921b491
-- statement:
--   If $nx<1$ , show that $1-nx>0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9901 (n x : ℝ) (h₁ : n * x < 1) : 1 - n * x > 0   :=  by sorry
