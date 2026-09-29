-- Prove2me | Theorems.Thm_lean_workbook_plus_76275
-- name    : lean_workbook_plus_76275
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/03642cfd-eb44-4048-951c-6f0a7eba9f0f
-- statement:
--   For $ c^3 - c$ , the values are $ 0,6,24,60,120,210,336,504,720$ . Let this be set $ C$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76275 {0, 6, 24, 60, 120, 210, 336, 504, 720} = {c^3 - c | c ∈ Finset.range 10}   :=  by sorry
