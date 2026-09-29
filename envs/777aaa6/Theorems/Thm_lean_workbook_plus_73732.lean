-- Prove2me | Theorems.Thm_lean_workbook_plus_73732
-- name    : lean_workbook_plus_73732
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/609f8d6b-aa86-4115-9d73-b45e0e544f45
-- statement:
--   Show that $ |x+y|=|x|+|y| \leftrightarrow x \cdot y \ge 0.$ ( If and only if )
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73732 (x y : ℝ) : |x + y| = |x| + |y| ↔ x*y ≥ 0   :=  by sorry
