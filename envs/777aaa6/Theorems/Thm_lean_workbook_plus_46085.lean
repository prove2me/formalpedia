-- Prove2me | Theorems.Thm_lean_workbook_plus_46085
-- name    : lean_workbook_plus_46085
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/77f1e89e-1149-43aa-bbec-f627391a7c0b
-- statement:
--   Check if the base case of the induction is correct: $2(cos (1-1) \theta) + 1 = 2(cos 0) + 1 = 2 \cdot 1 + 1 = 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46085 : 2 * Real.cos (0 * θ) + 1 = 3   :=  by sorry
