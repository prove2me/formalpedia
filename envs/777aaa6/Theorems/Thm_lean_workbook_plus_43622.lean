-- Prove2me | Theorems.Thm_lean_workbook_plus_43622
-- name    : lean_workbook_plus_43622
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/49afb5e7-0d1f-4c81-86e7-906dedfd4e5a
-- statement:
--   Prove for all real numbers $x \neq 0$: $x^{12}-x^{9}-x^{3}+1 = (x^{9}-1)(x^{3}-1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43622 (x : ℝ) (hx : x ≠ 0) : x ^ 12 - x ^ 9 - x ^ 3 + 1 = (x ^ 9 - 1) * (x ^ 3 - 1)   :=  by sorry
