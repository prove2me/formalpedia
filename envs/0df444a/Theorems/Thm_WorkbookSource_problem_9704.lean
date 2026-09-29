-- Prove2me | Theorems.Thm_WorkbookSource_problem_9704
-- name    : WorkbookSource.problem_9704
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:46:22.086774+00:00
-- url     : https://prove2.me/theorems/e1fff69e-aa0f-4f1d-98c5-1bed2bbe077c
-- title:
--   A quadratic bound for four weakly ordered numbers
-- statement:
--   Prove that if $ a\le b\le c\le d$, then $(a + b + c + d)^2\ge\(8(ac + bd)$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9704` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9704; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_9704 (a b c d : ℝ) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) : (a + b + c + d) ^ 2 ≥ 8 * (a * c + b * d)  :=  by sorry
