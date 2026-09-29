-- Prove2me | Theorems.Thm_lean_workbook_plus_82094
-- name    : lean_workbook_plus_82094
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/97b1ed25-8fb8-4b5f-9def-8a39f9e60374
-- statement:
--   $sin(A + C).sinB + sin^2B = sinB(sinA.cosC + cosA.sinC) + sin^2B$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82094 : ∀ A B C : ℝ, sin (A + C) * sin B + sin B ^ 2 = sin B * (sin A * cos C + cos A * sin C) + sin B ^ 2   :=  by sorry
