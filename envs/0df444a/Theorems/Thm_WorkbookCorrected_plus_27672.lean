-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_27672
-- name    : WorkbookCorrected.plus_27672
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T13:12:27.780923+00:00
-- url     : https://prove2.me/theorems/f1e5483e-cf81-48fd-8054-5ef4f4dcfa0c
-- title:
--   An inequality from a product of adjacent sums
-- statement:
--   Let $0<a,b,c<1$ satisfy $(a+b)(b+c)=1$. Then
--   \[b^2\ge(1-a)(1-c).\]
--
--   Formalization Note: The source formalization added $a+b+c=1$, an assumption absent from the source and incompatible with its other hypotheses. This correction removes that added assumption and proves the stated inequality from the original interval and product conditions.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_27672 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_27672; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_27672 (a b c : ℝ) (ha : 0<a ∧ a<1) (hb : 0<b ∧ b<1) (hc : 0<c ∧ c<1) (h : (a+b)*(b+c)=1) : b^2 ≥ (1-a)*(1-c) := by sorry
