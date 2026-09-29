-- Prove2me | Theorems.Thm_WorkbookSource_plus_34677
-- name    : WorkbookSource.plus_34677
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:09:33.708609+00:00
-- url     : https://prove2.me/theorems/8d8a48c9-7ac7-428c-ae97-7204e298fe1b
-- title:
--   A pairwise-product bound from a quotient
-- statement:
--   From the inequality $\frac{(a+b+c)^2}{a^2+b^2+c^2+3} \leq 1$, deduce that $ab+bc+ca \leq \frac{3}{2}$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_34677` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_34677; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_34677 (a b c : ℝ) : (a + b + c) ^ 2 / (a ^ 2 + b ^ 2 + c ^ 2 + 3) ≤ 1 → a * b + b * c + c * a ≤ 3 / 2   :=  by sorry
