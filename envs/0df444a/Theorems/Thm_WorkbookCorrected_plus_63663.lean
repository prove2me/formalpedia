-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_63663
-- name    : WorkbookCorrected.plus_63663
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T13:57:22.93791+00:00
-- url     : https://prove2.me/theorems/1b9379a4-f3d5-461d-b903-1b04c7470e52
-- title:
--   A product bound from reciprocal weighted sums
-- statement:
--   Let $a,b>0$ and $\frac{1}{a+9b}+\frac{1}{b+9a} = \frac{5}{24} $ . Prove that\n $$ab\leq 1$$
--
--   Formalization Note: The original formalization added a+b=1, absent from the source. This correction removes that assumption and proves the original product bound using the reciprocal equation and positivity.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_63663 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_63663; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_63663 (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (h : 1/(a+9*b)+1/(b+9*a)=5/24) : a*b ≤ 1 := by sorry
