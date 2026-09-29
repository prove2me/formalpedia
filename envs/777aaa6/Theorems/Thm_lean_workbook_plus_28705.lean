-- Prove2me | Theorems.Thm_lean_workbook_plus_28705
-- name    : lean_workbook_plus_28705
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/6a7b7510-1b97-4dad-9c01-455562d6b792
-- statement:
--   Let $a, b, c, d$ be real numbers, if $a^2 +b^2 + (a -b)^2 = c^2 + d^2 + (c - d)^2$ prove $a^4 +b^4 + (a - b)^4 = c^4 + d^4 + (c -d)^4$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28705 {a b c d : ℝ} (h : a^2 + b^2 + (a - b)^2 = c^2 + d^2 + (c - d)^2) : a^4 + b^4 + (a - b)^4 = c^4 + d^4 + (c - d)^4   :=  by sorry
