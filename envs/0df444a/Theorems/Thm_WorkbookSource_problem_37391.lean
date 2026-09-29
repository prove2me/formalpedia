-- Prove2me | Theorems.Thm_WorkbookSource_problem_37391
-- name    : WorkbookSource.problem_37391
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:39:40.317134+00:00
-- url     : https://prove2.me/theorems/d6780d78-2808-4668-8c26-198a5a8debb7
-- title:
--   Nonnegativity of a triangle-side quotient
-- statement:
--   Let $a,b,c\ge0$ satisfy the strict triangle inequalities. Then
--
--   $$\frac{a+c-b}{2(a+b+c)(c+a)}\ge0.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_37391` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_37391; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_37391 {a b c : ℝ} (hx: a >= 0 ∧ b >= 0 ∧ c >= 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : (a + c - b) / (2 * (a + b + c) * (c + a)) ≥ 0  :=  by sorry
