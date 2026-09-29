-- Prove2me | Theorems.Thm_lean_workbook_plus_19562
-- name    : lean_workbook_plus_19562
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/c0eb726b-3715-44ef-9f36-7b8a6a27eee3
-- statement:
--   $\sin^2x-\sin^2y=\sin(x+y)\sin (x-y)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19562 (x y : ℝ) : (sin x)^2 - (sin y)^2 = sin (x + y) * sin (x - y)   :=  by sorry
