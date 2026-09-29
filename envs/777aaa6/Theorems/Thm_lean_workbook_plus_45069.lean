-- Prove2me | Theorems.Thm_lean_workbook_plus_45069
-- name    : lean_workbook_plus_45069
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/674e3a53-e919-4f37-b191-7b84c6838a21
-- statement:
--   Prove that $\cos 4x = 8\cos^4 x - 8 \cos ^2 x + 1$ using the identity $\cos^4 x = \frac{4 \cos 2x + \cos 4x + 3}{8}$ and $\cos^2 x = \frac{\cos 2x + 1}{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45069 (x : ℝ) : (8 * cos x ^ 4 - 8 * cos x ^ 2 + 1) = cos (4 * x)   :=  by sorry
