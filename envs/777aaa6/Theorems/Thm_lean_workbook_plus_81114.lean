-- Prove2me | Theorems.Thm_lean_workbook_plus_81114
-- name    : lean_workbook_plus_81114
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/7097b297-aca5-499a-a66b-17b3a0b4291e
-- statement:
--   Prove that $\cos 3x = \cos x(4\cos^2 x - 3)$ using the sum-to-product identities for cosine.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81114 x : Real.cos (3 * x) = Real.cos x * (4 * (Real.cos x)^2 - 3)   :=  by sorry
