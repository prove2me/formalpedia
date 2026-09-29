-- Prove2me | Theorems.Thm_WorkbookSource_problem_10967
-- name    : WorkbookSource.problem_10967
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:46:40.814317+00:00
-- url     : https://prove2.me/theorems/d2636c11-8aed-497d-80a2-9aafafd77e8b
-- title:
--   A sum-of-squares bound from a quadratic constraint
-- statement:
--   Prove that $a^2+b^2+c^2 \ge 12$ given $a,b,c>0$ and $3(a^2+b^2+c^2)+2(a+b+c)=48$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_10967` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_10967; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_10967 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0): 3 * (a ^ 2 + b ^ 2 + c ^ 2) + 2 * (a + b + c) = 48 → a ^ 2 + b ^ 2 + c ^ 2 ≥ 12  :=  by sorry
