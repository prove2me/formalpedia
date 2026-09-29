-- Prove2me | Theorems.Thm_lean_workbook_plus_43951
-- name    : lean_workbook_plus_43951
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/c4eabcf4-12c7-4f22-a9cb-b80099ffcbc7
-- statement:
--   Solve for $x$: $x^2 - 2x - 1 = 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43951 : x^2 - 2*x - 1 = 0 ↔ x = 1 + Real.sqrt 2 ∨ x = 1 - Real.sqrt 2   :=  by sorry
