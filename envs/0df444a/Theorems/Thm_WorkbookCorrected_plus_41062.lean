-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_41062
-- name    : WorkbookCorrected.plus_41062
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T14:05:25.383095+00:00
-- url     : https://prove2.me/theorems/6f9ae3c5-6226-4871-bb2f-f3d3a62bbf26
-- title:
--   A sum-of-squares upper bound from a reciprocal difference constraint
-- statement:
--   Let $a,b,c\geq1$ and $a+b+c=\frac{1}{a}+\frac{1}{b}+\frac{1}{c}+6.$ Prove that $a^2+b^2+c^2\leq 21+6\sqrt{10}$
--
--   Formalization Note: The original formalization added abc=1, which is absent from the source. This correction removes that extra hypothesis and proves the source upper bound using a,b,c≥1 and the reciprocal relation alone.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_41062 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_41062; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_41062 (a b c : ℝ) (ha : 1≤a) (hb : 1≤b) (hc : 1≤c)
    (h : a+b+c=1/a+1/b+1/c+6) : a^2+b^2+c^2 ≤ 21+6*Real.sqrt 10 := by sorry
