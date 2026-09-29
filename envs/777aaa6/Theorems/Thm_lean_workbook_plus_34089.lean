-- Prove2me | Theorems.Thm_lean_workbook_plus_34089
-- name    : lean_workbook_plus_34089
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/40b04594-f05f-4706-b1b7-7a6e7219058a
-- statement:
--   Prove that $\left( ca-ab\right) ^{2}+\left( ab-bc\right) ^{2}+\left( bc-ca\right) ^{2}\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34089 (a b c : ℝ) : (c * a - b * a) ^ 2 + (b * a - c * b) ^ 2 + (c * b - a * c) ^ 2 ≥ 0   :=  by sorry
