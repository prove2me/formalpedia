-- Prove2me | Theorems.Thm_lean_workbook_plus_45517
-- name    : lean_workbook_plus_45517
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/2a725a64-9e89-4c55-9506-faa394eaa616
-- statement:
--   By Cauchy-Schwarz inequality, $ ab +bc+ ca<=a^2+b^2+c^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45517 (a b c: ℝ): a * b + b * c + c * a <= a ^ 2 + b ^ 2 + c ^ 2   :=  by sorry
