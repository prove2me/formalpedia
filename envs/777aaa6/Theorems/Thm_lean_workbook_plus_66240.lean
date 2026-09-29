-- Prove2me | Theorems.Thm_lean_workbook_plus_66240
-- name    : lean_workbook_plus_66240
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/74443205-79d5-4e5a-b0c3-7de4ba6fb86a
-- statement:
--   Solve for $p$:\n\n $$ p = \frac{1+ \sqrt{q^3+5}}{2} $$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66240 (p q : ℝ) : p = (1 + Real.sqrt (q^3 + 5)) / 2 ↔ p = (1 + Real.sqrt (q^3 + 5)) / 2   :=  by sorry
