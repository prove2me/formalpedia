-- Prove2me | Theorems.Thm_lean_workbook_plus_12107
-- name    : lean_workbook_plus_12107
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/08409d26-7ca9-4834-b861-b5c52a65c695
-- statement:
--   Given that $r$ and $s$ are the roots of $2x^2+bx+c$ and $r-s=20$, find $r^2-2rs+s^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12107 (r s : ℝ) (h₁ : 2*r^2 + b*r + c = 0) (h₂ : 2*s^2 + b*s + c = 0) (h₃ : r - s = 20) : r^2 - 2*r*s + s^2 = 400   :=  by sorry
