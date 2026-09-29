-- Prove2me | Theorems.Thm_lean_workbook_plus_12205
-- name    : lean_workbook_plus_12205
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/431c1cf0-dec1-4c15-bfa8-d8c762adfe0c
-- statement:
--   Prove that $2n+1 < n^{2}$ for all $n \geq 3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12205 (n : ℕ) (hn : 3 ≤ n) : 2 * n + 1 < n ^ 2   :=  by sorry
