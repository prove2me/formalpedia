-- Prove2me | Theorems.Thm_WorkbookSource_plus_81434
-- name    : WorkbookSource.plus_81434
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:11:29.436123+00:00
-- url     : https://prove2.me/theorems/555673a0-ac78-4281-8d78-9c117322a94c
-- title:
--   A quadratic equality excludes a nondegenerate triangle
-- statement:
--   Given $a^2+b^2+c^2=2(ab+bc+ca)$, show that $a$, $b$, and $c$ do not form the sides of a triangle.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_81434` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_81434; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_81434 (a b c : ℝ) (hx: a^2 + b^2 + c^2 = 2 * (a * b + b * c + c * a)) : ¬(a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b > c ∧ a + c > b ∧ b + c > a)   :=  by sorry
