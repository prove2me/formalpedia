-- Prove2me | Theorems.Thm_lean_workbook_plus_53862
-- name    : lean_workbook_plus_53862
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/a0a3251d-617a-41a1-b239-a70a9f4e5b9f
-- statement:
--   Prove that $a[(a^2-1)^2+a^2]=2 \implies a > 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53862 (a : ℝ) : a * ((a ^ 2 - 1) ^ 2 + a ^ 2) = 2 → a > 0   :=  by sorry
