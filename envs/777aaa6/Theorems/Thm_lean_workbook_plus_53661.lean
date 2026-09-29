-- Prove2me | Theorems.Thm_lean_workbook_plus_53661
-- name    : lean_workbook_plus_53661
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/392f01f0-3fa8-4728-893b-107df0323620
-- statement:
--   Find \\(n^3-2n^2+n\\) when \\(n=258\\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53661 (n : ℕ) (hn : n = 258) : n^3 - 2*n^2 + n = 258^3 - 2 * 258^2 + 258   :=  by sorry
