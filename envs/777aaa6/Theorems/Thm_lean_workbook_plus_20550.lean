-- Prove2me | Theorems.Thm_lean_workbook_plus_20550
-- name    : lean_workbook_plus_20550
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/4f697f8a-770a-4c94-84ac-d0d9775e448f
-- statement:
--   Prove that $2|a+b+c| \leq |a+b| + |b+c| + |c+a|$ for all real numbers $a, b, c$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20550 (a b c : ℝ) : 2 * |a + b + c| ≤ |a + b| + |b + c| + |c + a|   :=  by sorry
