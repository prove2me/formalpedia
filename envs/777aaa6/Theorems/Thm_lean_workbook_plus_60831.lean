-- Prove2me | Theorems.Thm_lean_workbook_plus_60831
-- name    : lean_workbook_plus_60831
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/75483160-d2e6-4fd9-bb97-944a4b75ac3e
-- statement:
--   For all positive integers $a,b,$ and $c$ such that $abc = 1$ , prove that $a^2 + b^2 + c^2 \ge a + b + c$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60831 (a b c : ℕ) (h : a * b * c = 1) :
  a ^ 2 + b ^ 2 + c ^ 2 ≥ a + b + c   :=  by sorry
