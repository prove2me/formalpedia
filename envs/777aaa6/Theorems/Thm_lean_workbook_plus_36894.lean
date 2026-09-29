-- Prove2me | Theorems.Thm_lean_workbook_plus_36894
-- name    : lean_workbook_plus_36894
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/4d572bdd-0f7a-4fb2-846d-e024132ab284
-- statement:
--   $ \frac {x}{1 + x^2}\leq\frac {1}{2},$ with equality iff $ x = 1.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36894 (x : ℝ) : x / (1 + x ^ 2) ≤ 1 / 2 ∧ (x = 1 ↔ x / (1 + x ^ 2) = 1 / 2)   :=  by sorry
