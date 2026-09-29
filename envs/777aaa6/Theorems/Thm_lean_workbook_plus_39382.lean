-- Prove2me | Theorems.Thm_lean_workbook_plus_39382
-- name    : lean_workbook_plus_39382
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/0e0ce773-02f8-4072-8dce-614cbed86cbb
-- statement:
--   Prove that $3\sin x - 4\sin^3 x = \sin 3x$ using the identities $\cos 2x = 2\cos^2 x - 1 = 1 - 2\sin^2 x$ and the sum-to-product identities for sine and cosine.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39382 x : 3 * Real.sin x - 4 * (Real.sin x)^3 = Real.sin (3 * x)   :=  by sorry
