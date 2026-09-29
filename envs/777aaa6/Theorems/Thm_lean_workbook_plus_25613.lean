-- Prove2me | Theorems.Thm_lean_workbook_plus_25613
-- name    : lean_workbook_plus_25613
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/e6c28d4b-b4c2-4ad9-9e06-368870c9c38f
-- statement:
--   Prove that $g(y)=4*9^{y}-6^{y}-3\ge 0$ when $y\ge 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25613 (y : ℕ) (hy : 0 ≤ y) : 4 * 9^y - 6^y - 3 ≥ 0   :=  by sorry
