-- Prove2me | Theorems.Thm_lean_workbook_plus_58650
-- name    : lean_workbook_plus_58650
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/d195e587-cb0f-480b-a678-5869f29bb602
-- statement:
--   We have $ f(f(0))=f(0)$ and, since $ f(x)$ is injective, $ f(0)=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58650 {f : ℝ → ℝ} (hf : Function.Injective f) (h : f (f 0) = f 0) : f 0 = 0   :=  by sorry
