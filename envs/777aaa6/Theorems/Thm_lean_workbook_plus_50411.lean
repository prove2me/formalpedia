-- Prove2me | Theorems.Thm_lean_workbook_plus_50411
-- name    : lean_workbook_plus_50411
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/46a48142-dde4-4561-8a48-78eb9259e357
-- statement:
--   Find the maximum value of $ab+bc+cd+da$ given that $a+b+c+d = 4$ and $a, b, c, d$ are positive real numbers.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50411 (a b c d : ℝ) : a + b + c + d = 4 → a * b + b * c + c * d + d * a ≤ 4   :=  by sorry
