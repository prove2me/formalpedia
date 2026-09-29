-- Prove2me | Theorems.Thm_lean_workbook_plus_30742
-- name    : lean_workbook_plus_30742
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/0768dc9b-38bd-4704-92d1-c1e058a67227
-- statement:
--   Prove that for all real numbers n other than $0$ , that $n^0$ = 1.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30742 (n : ℝ) (hn : n ≠ 0) : n^0 = 1   :=  by sorry
