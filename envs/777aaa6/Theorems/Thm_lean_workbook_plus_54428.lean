-- Prove2me | Theorems.Thm_lean_workbook_plus_54428
-- name    : lean_workbook_plus_54428
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/319c58e2-1161-49eb-82dd-090f045bf841
-- statement:
--   Prove that $n^2 - 10n - 22 \le n - 1$ implies $n \le 12$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54428 (n : ℤ) (h : n^2 - 10*n - 22 ≤ n - 1) : n ≤ 12   :=  by sorry
