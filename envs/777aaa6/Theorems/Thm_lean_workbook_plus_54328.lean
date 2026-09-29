-- Prove2me | Theorems.Thm_lean_workbook_plus_54328
-- name    : lean_workbook_plus_54328
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/437d26c9-f495-4f44-aa19-af1b1e8eb03d
-- statement:
--   Given $ x \ge y$, prove that $ e^x - e^y \ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54328 (x y : ℝ) (h : x ≥ y) : exp x - exp y ≥ 0   :=  by sorry
