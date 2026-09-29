-- Prove2me | Theorems.Thm_lean_workbook_plus_40973
-- name    : lean_workbook_plus_40973
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/155679ae-0397-4c10-8892-e48c29f36be1
-- statement:
--   note that: $x^{2}-x(\sin x+\cos x)+\sin x\cos x=(x-\sin x)(x-\cos x)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40973 (x : ℝ) : x^2 - x * (sin x + cos x) + sin x * cos x = (x - sin x) * (x - cos x)   :=  by sorry
