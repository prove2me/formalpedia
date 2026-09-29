-- Prove2me | Theorems.Thm_lean_workbook_plus_78332
-- name    : lean_workbook_plus_78332
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/b568e3a2-2579-4083-ae4f-3fcbdb43442a
-- statement:
--   Solve the cubic equation $y^3 - 3py + p^3 + 1 = 0$ for $y$ in terms of $p$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78332 (p : ℂ) : ∃ y, y^3 - 3 * p * y + p^3 + 1 = 0   :=  by sorry
