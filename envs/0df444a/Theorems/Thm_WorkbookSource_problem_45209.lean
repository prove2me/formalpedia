-- Prove2me | Theorems.Thm_WorkbookSource_problem_45209
-- name    : WorkbookSource.problem_45209
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:50:55.85077+00:00
-- url     : https://prove2.me/theorems/8770964c-46f6-4947-aec9-85a04b73f9dd
-- title:
--   A mixed square-cube bound at sum three
-- statement:
--   Let $a, b, c\geq 0$ and $a+b+c=3$ .Then $$a^2+b^2+c^3\leq 27$$
--
--   Source: InternLM Lean-Workbook, record lean_workbook_45209; Apache-2.0. Complete source proposition preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_45209; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_45209 (a b c : ℝ) (ha : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0) (hab : a + b + c = 3) : a ^ 2 + b ^ 2 + c ^ 3 ≤ 27  :=  by sorry
