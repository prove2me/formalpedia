-- Prove2me | Theorems.Thm_lean_workbook_plus_70928
-- name    : lean_workbook_plus_70928
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/0c9a05c4-f910-4188-b8aa-890da08e7ad8
-- statement:
--   For $x\geq 0$ it is true that $e^{-x} \leq 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70928 : ∀ x ≥ 0, exp (-x) ≤ 1   :=  by sorry
