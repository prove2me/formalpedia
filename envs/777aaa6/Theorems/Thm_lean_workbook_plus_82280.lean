-- Prove2me | Theorems.Thm_lean_workbook_plus_82280
-- name    : lean_workbook_plus_82280
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/52e4d234-183e-4189-96b9-a4712b9bb8f8
-- statement:
--   LHS $= \sin(2b-2c)\cos a+\sin(b-c)\cos(a-b-c)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82280 (a b c : ℝ) : sin (2 * b - 2 * c) * cos a + sin (b - c) * cos (a - b - c) = sin (2 * b - 2 * c) * cos a + sin (b - c) * cos (a - b - c)   :=  by sorry
