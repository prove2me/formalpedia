-- Prove2me | Theorems.Thm_lean_workbook_plus_3220
-- name    : lean_workbook_plus_3220
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/00e120e8-b3bb-4796-9adc-7fb51b0f4ea9
-- statement:
--   Prove that if $0 < a < 2$ , then $a < \sqrt{2a} < 2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3220 (a : ℝ) (h : 0 < a ∧ a < 2) : a < Real.sqrt (2 * a) ∧ Real.sqrt (2 * a) < 2   :=  by sorry
