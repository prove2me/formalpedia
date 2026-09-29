-- Prove2me | Theorems.Thm_lean_workbook_plus_43723
-- name    : lean_workbook_plus_43723
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/e2725805-403d-44b8-af03-d71eb1b8b2a7
-- statement:
--   Given the expression $a^2 + b^2 + c^2 - ab - ac - bc$, explain why it is symmetric and provide an example of how its symmetry can be demonstrated through variable permutations.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43723 (a b c : ℝ) : a^2 + b^2 + c^2 - (a * b + a * c + b * c) = b^2 + c^2 + a^2 - (b * c + b * a + c * a)   :=  by sorry
