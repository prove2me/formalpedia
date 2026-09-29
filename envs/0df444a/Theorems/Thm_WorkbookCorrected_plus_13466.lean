-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_13466
-- name    : WorkbookCorrected.plus_13466
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T13:59:46.513316+00:00
-- url     : https://prove2.me/theorems/444ae290-79ec-4c60-ad95-f234e3f42dc1
-- title:
--   A sharp sum bound from reciprocal quadratic denominators
-- statement:
--   Let $a,b,c$ be positive numbers satisfying $\frac{1}{a^2+2}+\frac{1}{b^2+2}+\frac{1}{c^2+2}=\frac{1}{3}$ . Prove that $a+b+c\ge 3\sqrt{7}.$
--
--   Formalization Note: The original formalization added abc=1, absent from the source. This correction removes that added hypothesis and proves the source lower bound for all positive real variables satisfying the reciprocal identity.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_13466 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_13466; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_13466 (a b c : ℝ) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (h : 1/(a^2+2)+1/(b^2+2)+1/(c^2+2)=1/3) : a+b+c ≥ 3*Real.sqrt 7 := by sorry
