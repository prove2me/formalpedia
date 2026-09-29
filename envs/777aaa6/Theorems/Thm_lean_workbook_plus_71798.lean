-- Prove2me | Theorems.Thm_lean_workbook_plus_71798
-- name    : lean_workbook_plus_71798
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/7f8256cb-355e-449c-8809-7f699e5d917c
-- statement:
--   Prove: $ \cos 3x = \cos^3 x - 3\cos x \sin^2 x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71798 x : Real.cos (3 * x) = Real.cos x ^ 3 - 3 * Real.cos x * Real.sin x ^ 2   :=  by sorry
