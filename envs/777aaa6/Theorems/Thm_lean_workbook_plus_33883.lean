-- Prove2me | Theorems.Thm_lean_workbook_plus_33883
-- name    : lean_workbook_plus_33883
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/1da81834-a1d2-47d1-be5b-400b8d0589fb
-- statement:
--   If $a+b+c=0$ then $a^5+b^5+c^5=-5ab(a+b)(a^2+ab+b^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33883 {a b c : ℤ} (h : a + b + c = 0) : a^5 + b^5 + c^5 = -5 * a * b * (a + b) * (a^2 + a * b + b^2)   :=  by sorry
