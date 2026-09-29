-- Prove2me | Theorems.Thm_lean_workbook_plus_74549
-- name    : lean_workbook_plus_74549
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/b7100ee7-58db-4579-bf1c-bf813900a497
-- statement:
--   Prove that $\sin 3x = \sin x(3 - 4\sin^2 x)$ using the sum-to-product identities for sine.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74549 x : Real.sin (3 * x) = Real.sin x * (3 - 4 * (Real.sin x)^2)   :=  by sorry
