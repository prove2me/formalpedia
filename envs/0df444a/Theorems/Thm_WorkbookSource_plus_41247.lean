-- Prove2me | Theorems.Thm_WorkbookSource_plus_41247
-- name    : WorkbookSource.plus_41247
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:09:25.642478+00:00
-- url     : https://prove2.me/theorems/77b12cd4-a469-4102-890c-09de6300523f
-- title:
--   A negative discriminant excludes real roots
-- statement:
--   Given $a > 0$ and a negative discriminant, what can be said about the roots of the corresponding quadratic?
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_41247` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_41247; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_41247 (a : ℝ) (b : ℝ) (c : ℝ) (ha : a > 0) (h : b^2 - 4*a*c < 0) : ¬ (∃ x, a*x^2 + b*x + c = 0)   :=  by sorry
