-- Prove2me | Theorems.Thm_lean_workbook_plus_78661
-- name    : lean_workbook_plus_78661
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/4bcaf6f0-0497-4d86-8391-8cfab724023a
-- statement:
--   Is it $\frac{4}{52} \frac{3}{51}$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78661 (h : 52 ≠ 0 ∧ 51 ≠ 0) : (4 : ℚ) / 52 * (3 / 51) = (4 * 3) / (52 * 51)   :=  by sorry
