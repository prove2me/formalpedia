-- Prove2me | Theorems.Thm_lean_workbook_plus_32065
-- name    : lean_workbook_plus_32065
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/afbf9092-8a24-4e17-b405-64b1e55978d6
-- statement:
--   Given the inequality $8 \geq 8\sqrt{abc}$, deduce that $\sqrt{abc} \leq 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32065 : 8 ≥ 8 * Real.sqrt (a * b * c) → Real.sqrt (a * b * c) ≤ 1   :=  by sorry
