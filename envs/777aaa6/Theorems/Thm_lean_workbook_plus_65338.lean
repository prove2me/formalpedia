-- Prove2me | Theorems.Thm_lean_workbook_plus_65338
-- name    : lean_workbook_plus_65338
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/2d7cfdc5-41ef-435f-8363-84227e74ed9b
-- statement:
--   Let $ a, b, c >0$ . Prove that: $ \boxed{a^4+b^4+c^4\ge (a+b+c)abc}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65338 (a b c : ℝ) (ha : 0<a) (hb : 0<b) (hc : 0<c) : a^4 + b^4 + c^4 >= (a+b+c)*a*b*c   :=  by sorry
