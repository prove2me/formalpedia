-- Prove2me | Theorems.Thm_lean_workbook_plus_47390
-- name    : lean_workbook_plus_47390
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/40dcf87f-ccdf-4d56-a4da-5d2e138974b0
-- statement:
--   Prove that $(a+b)^{2}+(3\sqrt{ab})^{2}\geq 6(a+b)\sqrt{ab}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47390 (a b : ℝ) : (a+b)^2 + (3 * Real.sqrt (a * b))^2 >= 6 * (a + b) * Real.sqrt (a * b)   :=  by sorry
