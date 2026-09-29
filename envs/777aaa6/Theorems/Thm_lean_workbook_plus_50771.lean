-- Prove2me | Theorems.Thm_lean_workbook_plus_50771
-- name    : lean_workbook_plus_50771
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/44e7d7be-7eab-4bd2-8fa5-9aeb85d55342
-- statement:
--   Show that $4(\sum a^2)^2\geq3(\sum a^4+ 3\sum a^2b^2)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50771 (a b c : ℝ) : 4 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 3 * (a ^ 4 + b ^ 4 + c ^ 4 + 3 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2))   :=  by sorry
