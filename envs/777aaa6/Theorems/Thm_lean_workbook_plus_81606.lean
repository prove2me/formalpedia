-- Prove2me | Theorems.Thm_lean_workbook_plus_81606
-- name    : lean_workbook_plus_81606
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/949d65d1-2d18-4ab0-9f4b-284043a969aa
-- statement:
--   Find the minimum and maximum values of the function $f(x) = (\sin^2(x) + 1)(2\cos^2(x) + 1)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81606 (x : ℝ) : 2 ≤ (sin x ^ 2 + 1) * (2 * cos x ^ 2 + 1) ∧ (sin x ^ 2 + 1) * (2 * cos x ^ 2 + 1) ≤ 4   :=  by sorry
