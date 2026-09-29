-- Prove2me | Theorems.Thm_lean_workbook_plus_46933
-- name    : lean_workbook_plus_46933
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/bb9ba41a-f8bb-4291-a1b0-358d9fb36c0c
-- statement:
--   What is $\frac{\sqrt{1 - a^2} - 1}{a} \cdot \frac{\sqrt{1 - a^2} + 1}{a}$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46933 (a : ℝ) (ha : 0 < a) (hab : a ≠ 1) : (Real.sqrt (1 - a^2) - 1) / a * (Real.sqrt (1 - a^2) + 1) / a = (Real.sqrt (1 - a^2) - 1) * (Real.sqrt (1 - a^2) + 1) / a^2   :=  by sorry
