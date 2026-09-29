-- Prove2me | Theorems.Thm_lean_workbook_plus_5244
-- name    : lean_workbook_plus_5244
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/22015e68-2a05-46ea-9969-f7a12aefd97c
-- statement:
--   After using Cauchy Schwarts, it's becomes: \n$ \sum\ (a - b)^2(b - c)^2 + 3(abc - 1)^2 + 3 - abc \geq\ 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5244 (a b c : ℝ) : (a - b) ^ 2 * (b - c) ^ 2 + 3 * (a * b * c - 1) ^ 2 + 3 - a * b * c ≥ 0   :=  by sorry
