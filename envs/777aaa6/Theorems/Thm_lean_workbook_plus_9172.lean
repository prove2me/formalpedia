-- Prove2me | Theorems.Thm_lean_workbook_plus_9172
-- name    : lean_workbook_plus_9172
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/4e9bb3cc-d230-4c64-95ec-3620a3b422e5
-- statement:
--   It's Cauchy-Schwarz: $(1^2+1^2+1^2)(a^2+b^2+c^2)\geq (a+b+c)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9172 {a b c : ℝ} : (1^2 + 1^2 + 1^2) * (a^2 + b^2 + c^2) ≥ (a + b + c)^2   :=  by sorry
