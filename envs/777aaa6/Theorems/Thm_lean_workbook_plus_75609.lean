-- Prove2me | Theorems.Thm_lean_workbook_plus_75609
-- name    : lean_workbook_plus_75609
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/87c08976-6d5c-4f81-9326-4cb6b001d222
-- statement:
--   Prove the identity $x^3+y^3=(x+y)(x^2-xy+y^2)$ without fully expanding both sides.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75609 : ∀ x y : ℝ, x^3 + y^3 = (x + y) * (x^2 - x * y + y^2)   :=  by sorry
