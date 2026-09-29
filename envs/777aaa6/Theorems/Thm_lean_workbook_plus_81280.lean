-- Prove2me | Theorems.Thm_lean_workbook_plus_81280
-- name    : lean_workbook_plus_81280
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/a27f05dc-67c1-4860-b71e-8f1cc0c2430e
-- statement:
--   If $a>0$ and $b^2-4ac<0$ then $ax^2+bx+c>0$ for all value of $x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81280 (a b c x: ℝ) (ha : a > 0) (h : b^2 - 4 * a * c < 0) : a * x^2 + b * x + c > 0   :=  by sorry
