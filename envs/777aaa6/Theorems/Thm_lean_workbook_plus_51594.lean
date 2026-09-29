-- Prove2me | Theorems.Thm_lean_workbook_plus_51594
-- name    : lean_workbook_plus_51594
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/4eec50c4-7947-4708-aebe-e3f9f4fea509
-- statement:
--   Find the minimum value of $2a^8 + 2b^6 + a^4 - b^3 - 2a^2 - 2$ for all $a, b \in \mathbb{R}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51594 (a b : ℝ) : (2 * a ^ 8 + 2 * b ^ 6 + a ^ 4 - b ^ 3 - 2 * a ^ 2 - 2 : ℝ) ≥ -11 / 4   :=  by sorry
