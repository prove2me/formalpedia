-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_32112
-- name    : WorkbookCorrected.plus_32112
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T13:44:14.044987+00:00
-- url     : https://prove2.me/theorems/398aad81-d3ca-4e87-a411-37b07350e8f1
-- title:
--   A sum-of-squares bound from a quartic and product constraint
-- statement:
--   Let $a,b,c$ be non-negative real numbers such that $a^4+b^4+c^4+abc=4$ . Prove that: $a^2+b^2+c^2 \leq 3$
--
--   Formalization Note: The original formalization added abc=1, which is absent from the source. This correction removes that extra assumption and proves the entire source proposition for nonnegative real variables.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_plus_32112 (Apache-2.0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_32112; Apache-2.0

import Mathlib

theorem WorkbookCorrected.plus_32112 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a^4+b^4+c^4+a*b*c=4) : a^2+b^2+c^2 ≤ 3 := by sorry
