-- Prove2me | Theorems.Thm_lean_workbook_plus_42805
-- name    : lean_workbook_plus_42805
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/19e3186c-c674-41da-98a0-cd1975995ab9
-- statement:
--   Show that $(1+x+y)^{2}\geq 3(x+y+xy)$, where $x$ and $y$ are real numbers.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42805 (x y : ℝ) : (1 + x + y) ^ 2 ≥ 3 * (x + y + x * y)   :=  by sorry
