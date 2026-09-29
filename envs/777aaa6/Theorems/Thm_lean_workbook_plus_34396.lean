-- Prove2me | Theorems.Thm_lean_workbook_plus_34396
-- name    : lean_workbook_plus_34396
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/36294fcf-0ce7-4adb-96c5-b5818394697e
-- statement:
--   Prove that the following inequality such that a and b are greater than 1 \n $\frac{a^2}{b-1}+\frac{b^2}{a-1}\ge {8}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34396 (a b : ℝ) (ha : 1 < a) (hb : 1 < b) : (a^2 / (b-1) + b^2 / (a-1)) ≥ 8   :=  by sorry
