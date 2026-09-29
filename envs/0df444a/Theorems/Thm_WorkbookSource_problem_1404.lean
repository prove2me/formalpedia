-- Prove2me | Theorems.Thm_WorkbookSource_problem_1404
-- name    : WorkbookSource.problem_1404
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:39:25.371468+00:00
-- url     : https://prove2.me/theorems/b057f788-de2c-4953-8a24-43c71a5913fb
-- title:
--   Triangle inequalities force positive variables
-- statement:
--   Given that $a + b > c$, $b + c > a$, and $c + a > b$, prove that $a > 0$, $b > 0$, and $c > 0$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1404` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1404; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_1404 (a b c : ℝ) (hab : a + b > c) (hbc : b + c > a) (hca : c + a > b) : a > 0 ∧ b > 0 ∧ c > 0  :=  by sorry
